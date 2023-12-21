use std::{borrow::{BorrowMut, Borrow}, env, process::exit};
use ark_std::{start_timer, end_timer};

use crate::{
    run::{keygen, mock, prove},
    scaffold::{AxiomCircuitScaffold, RawCircuitInput},
    subquery::{caller::SubqueryCaller, types::{AssignedHeaderSubquery, AssignedHiLo}},
};
use axiom_eth::{
    halo2_base::{
        gates::{circuit::BaseCircuitParams, GateChip, RangeChip},
        AssignedValue, Context,
        utils::BigPrimeField
    },
    halo2curves::bn256::Fr,
    halo2curves::bn256::G1Affine,
    halo2curves::{bn256::{G2Affine, Fq12}, serde::SerdeObject},
    halo2curves::ff::PrimeField,
    rlc::circuit::builder::RlcCircuitBuilder,
    Field,
    utils::encode_addr_to_field,
};
use halo2_ecc::{bn254::FpChip, fields::FieldChip};
use halo2_ecc::bn254::Fp2Chip;
use halo2_ecc::ecc::EccChip;
use halo2_ecc::bn254::Fp12Chip;
use halo2_ecc::bn254::pairing::PairingChip;

use dotenv::dotenv;
use ethers::providers::{Http, JsonRpcClient, Provider};
use ethers::types::Address;
use rand::{rngs::OsRng, RngCore};
use crate::subquery::types::AssignedStorageSubquery;

#[derive(Debug, Clone)]
struct MyCircuitInput {
    task_response_digest_g2coords: [u8; 128],
    agg_sig_g2coords: [u8; 128],
    g1_pubkey: [u8; 64],
    task_created_block: u64,
    quorum_g1_apk_x_slot: u64,
    quorum_g1_apk_y_slot: u64,
    operator_to_g1_pubkey_x_slot: u64,
    operator_to_g1_pubkey_y_slot: u64,
    bls_pubkey_registry_addr: [u8; 20],
    bls_pubkey_compendium_addr: [u8; 20],
}

#[derive(Debug, Clone)]
struct MyCircuitVirtualInput<F: Field> {
    task_response_digest_g2coords: [u8; 128],
    agg_sig_g2coords: [u8; 128],
    g1_pubkey: [u8; 64],
    bls_pubkey_registry_addr: AssignedValue<F>,
    bls_pubkey_compendium_addr: AssignedValue<F>,
    operator_to_g1_pubkey_x_slot: AssignedValue<F>,
    operator_to_g1_pubkey_y_slot: AssignedValue<F>,
    quorum_g1_apk_x_slot: AssignedValue<F>,
    quorum_g1_apk_y_slot: AssignedValue<F>,
    task_created_block: AssignedValue<F>,
}

fn vec_to_array(vec: Vec<u8>) -> Result<[u8; 128], &'static str> {
    if vec.len() == 128 {
        let mut arr = [0u8; 128];
        arr.copy_from_slice(&vec);
        Ok(arr)
    } else {
        Err("Vector does not have exactly 128 elements")
    }
}

fn vec_to_array64(vec: Vec<u8>) -> Result<[u8; 64], &'static str> {
    if vec.len() == 64 {
        let mut arr = [0u8; 64];
        arr.copy_from_slice(&vec);
        Ok(arr)
    } else {
        Err("Vector does not have exactly 64 elements")
    }
}

impl RawCircuitInput<Fr, MyCircuitVirtualInput<Fr>> for MyCircuitInput {
    fn default() -> Self {
        let mut rng = rand::thread_rng();
        let rand_g2_point = G2Affine::random(&mut rng);
        let rand_g2_point_arr = vec_to_array(rand_g2_point.to_raw_bytes()).unwrap();

        /// `R^2 = 2^512 mod r`
        /// `0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7`
        const R2: Fr = Fr::from_raw([
            1997599621687373223,
            6052339484930628067,
            10108755138030829701,
            150537098327114917,
        ]);

        /// `R^3 = 2^768 mod r`
        /// `0xcf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040`
        const R3: Fr = Fr::from_raw([
            6815310600030060608,
            3046857488260118200,
            9888997017309401069,
            934595103480898940,
        ]);

        let d0 = Fr::from_u64_digits(&[OsRng.next_u64(), OsRng.next_u64(), OsRng.next_u64(), OsRng.next_u64()]);
        let d1 = Fr::from_u64_digits(&[OsRng.next_u64(), OsRng.next_u64(), OsRng.next_u64(), OsRng.next_u64()]);
        // Convert to Montgomery form
        let sk_all_operators_circuit_g1_apk = d0 * R2 + d1 * R3;
        let signature: G2Affine = G2Affine::from(rand_g2_point * sk_all_operators_circuit_g1_apk);
        let signature_g2_vec = vec_to_array(signature.to_raw_bytes()).unwrap();
        let all_operators_circuit_g1_apk = G1Affine::from(G1Affine::generator() * sk_all_operators_circuit_g1_apk);
        
        println!("all_operators_circuit_g1_apk {}", all_operators_circuit_g1_apk.to_raw_bytes().len());

        MyCircuitInput {
            task_response_digest_g2coords: rand_g2_point_arr,
            agg_sig_g2coords: signature_g2_vec,
            g1_pubkey: vec_to_array64(all_operators_circuit_g1_apk.to_raw_bytes()).unwrap(),
            bls_pubkey_registry_addr: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            bls_pubkey_compendium_addr: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            operator_to_g1_pubkey_x_slot: 0,
            operator_to_g1_pubkey_y_slot: 0,
            quorum_g1_apk_x_slot: 0,
            quorum_g1_apk_y_slot: 0,
            task_created_block: 0,
        }
    }

    fn assign(&self, ctx: &mut Context<Fr>) -> MyCircuitVirtualInput<Fr> {

        MyCircuitVirtualInput {
            task_response_digest_g2coords: self.task_response_digest_g2coords,
            agg_sig_g2coords: self.agg_sig_g2coords,
            g1_pubkey: self.g1_pubkey,
            bls_pubkey_registry_addr: ctx.load_witness(encode_addr_to_field(&Address::from(self.bls_pubkey_registry_addr))),
            bls_pubkey_compendium_addr: ctx.load_witness(encode_addr_to_field(&Address::from(self.bls_pubkey_compendium_addr))),
            operator_to_g1_pubkey_x_slot: ctx.load_witness(Fr::from(self.operator_to_g1_pubkey_x_slot)),
            operator_to_g1_pubkey_y_slot: ctx.load_witness(Fr::from(self.operator_to_g1_pubkey_y_slot)),
            quorum_g1_apk_x_slot: ctx.load_witness(Fr::from(self.quorum_g1_apk_x_slot)),
            quorum_g1_apk_y_slot: ctx.load_witness(Fr::from(self.quorum_g1_apk_y_slot)),
            task_created_block: ctx.load_witness(Fr::from(self.task_created_block)),
        }
    }
}


pub fn encode_slot_to_lo_hi(slot: &[u8; 32]) -> (Fr, Fr) {
    let lo = u128::from_be_bytes(slot[16..].try_into().unwrap());
    let hi = u128::from_be_bytes(slot[..16].try_into().unwrap());
    (Fr::from_u128(lo), Fr::from_u128(hi))
}

#[derive(Debug, Clone)]
struct MyCircuit;
impl<P: JsonRpcClient> AxiomCircuitScaffold<P, Fr> for MyCircuit {
    type CircuitInput = MyCircuitInput;
    type VirtualCircuitInput = MyCircuitVirtualInput<Fr>;
    type FirstPhasePayload = ();

    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<Fr>,
        _range: &RangeChip<Fr>,
        subquery_caller: &mut SubqueryCaller<P, Fr>,
        callback: &mut Vec<AssignedHiLo<Fr>>,
        inputs: Self::VirtualCircuitInput,
    ) -> Self::FirstPhasePayload {

        let fq_chip = FpChip::<Fr>::new(_range, 88, 3); // 88 and 3 are fine ? looks like the range chip is already configured.
        let fq2_chip = Fp2Chip::new(&fq_chip);
        let pairing_chip = PairingChip::new(&fq_chip);

        // let gate = GateChip::<Fr>::new();
        let g1_chip = EccChip::new(&fq_chip);
        let g2_chip = EccChip::new(&fq2_chip);

        let task_response_digest_g2coords = G2Affine::from_raw_bytes(&inputs.task_response_digest_g2coords).unwrap();
        let agg_sig_g2coords = G2Affine::from_raw_bytes(&inputs.agg_sig_g2coords).unwrap();

        let g1_generator = g1_chip.assign_point::<G1Affine>(builder.base.borrow_mut().main(0), G1Affine::generator());
        let neg_rhs_g1 = g1_chip.negate(builder.base.borrow_mut().main(0), g1_generator);

        let aggregate_signature =
        g2_chip.assign_point::<G2Affine>(builder.base.borrow_mut().main(0), agg_sig_g2coords);

        
        let task_response_digest_bn254_g2 =
        g2_chip.assign_point::<G2Affine>(builder.base.borrow_mut().main(0), task_response_digest_g2coords);

        let g1_pubkey = G1Affine::from_raw_bytes(&inputs.g1_pubkey).unwrap();
        let signers_g1_apk = g1_chip.assign_point::<G1Affine>(builder.base.borrow_mut().main(0), g1_pubkey);

        let multi_paired = pairing_chip.multi_miller_loop(
            builder.base.borrow_mut().main(0),
            vec![
                (&signers_g1_apk, &task_response_digest_bn254_g2),
                (&neg_rhs_g1, &aggregate_signature),
            ],
        );

        let fq12_chip = Fp12Chip::new(&fq_chip);
        let result = fq12_chip.final_exp(builder.base.borrow_mut().main(0), multi_paired);
        let fq12_one = fq12_chip.load_constant(builder.base.borrow_mut().main(0), Fq12::one());
        let _verification_result = fq12_chip.is_equal(builder.base.borrow_mut().main(0), result, fq12_one);
        // verification_result.cell.unwrap().offset
        dbg!(_verification_result.value());

        // let slot_lo_hi = encode_slot_to_lo_hi(&inputs.operator_to_g1_pubkey_x_slot.value().to_bytes());
        // let slot_lo_loaded = builder.base.borrow_mut().main(0).load_witness(slot_lo_hi.0);
        // let slot_hi_loaded = builder.base.borrow_mut().main(0).load_witness(slot_lo_hi.1);
        
        // let storage_slot_subquery = AssignedStorageSubquery {
        //     block_number: inputs.task_created_block,
        //     addr: inputs.bls_pubkey_registry_addr,
        //     slot: AssignedHiLo {
        //         hi: slot_hi_loaded,
        //         lo: slot_lo_loaded
        //     },
        // };

        // let subquery = AssignedHeaderSubquery {
        //     block_number,
        //     field_idx,
        // };
        // let timestamp = subquery_caller.call(builder.base.borrow_mut().main(0), subquery);
        // callback.push(timestamp);
        // dbg!(builder.calculate_params(Some(20)));
        dbg!(builder.calculate_params(Some(20)));
    }
}

#[test]
pub fn test_keygen() {
    dotenv().ok();
    let keygen_time = start_timer!(|| "Key Gen generation time");
    let circuit = MyCircuit;
    let params = BaseCircuitParams {
        k: 17,
        num_advice_per_phase: vec![213],
        num_lookup_advice_per_phase: vec![38, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(16),
    };
    let client = Provider::<Http>::try_from("https://eth-goerli.g.alchemy.com/v2/JLBlHmi_gZ2Q8bEvbEN_pllNxX1-d6ge").unwrap();
    keygen(circuit, client, params, None);
    end_timer!(keygen_time);
}

#[test]
pub fn test_mock() {
    dotenv().ok();
    let circuit = MyCircuit;
    let params = BaseCircuitParams {
        k: 17,
        num_advice_per_phase: vec![213],
        num_lookup_advice_per_phase: vec![38, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(16),
    };
    let client = Provider::<Http>::try_from("https://eth-goerli.g.alchemy.com/v2/JLBlHmi_gZ2Q8bEvbEN_pllNxX1-d6ge").unwrap();
    mock(circuit, client, params, None);
}

#[test]
pub fn test_prove() {
    dotenv().ok();
    let circuit = MyCircuit;
    
    let params = BaseCircuitParams {
        k: 17,
        num_advice_per_phase: vec![213],
        num_lookup_advice_per_phase: vec![38, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(16),
    };
    let client = Provider::<Http>::try_from("https://eth-goerli.g.alchemy.com/v2/JLBlHmi_gZ2Q8bEvbEN_pllNxX1-d6ge").unwrap();
    let pk = keygen(circuit.clone(), client.clone(), params.clone(), None);
    prove(circuit, client, params, None, pk);
}
