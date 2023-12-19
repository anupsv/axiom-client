use std::{borrow::BorrowMut, env};

use crate::{
    run::{keygen, mock, prove},
    scaffold::{AxiomCircuitScaffold, RawCircuitInput},
    subquery::{caller::SubqueryCaller, types::{AssignedHeaderSubquery, AssignedHiLo}},
};
use axiom_eth::{
    halo2_base::{
        gates::{circuit::BaseCircuitParams, GateChip, RangeChip},
        AssignedValue, Context,
    },
    halo2curves::bn256::Fr,
    halo2curves::bn256::G1Affine,
    halo2curves::bn256::G2Affine,
    halo2curves::ff::PrimeField,
    rlc::circuit::builder::RlcCircuitBuilder,
    Field,
    utils::encode_addr_to_field,
};
use halo2_ecc::bn254::FpChip;
use halo2_ecc::bn254::Fp2Chip;
use halo2_ecc::bn254::pairing::PairingChip;

use dotenv::dotenv;
use ethers::providers::{Http, JsonRpcClient, Provider};
use ethers::types::Address;
use crate::subquery::types::AssignedStorageSubquery;

#[derive(Debug, Clone)]
struct MyCircuitInput {
    task_response_digest_g2coords: [u8; 128],
    agg_sig_g2coords: [u8; 128],
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
    bls_pubkey_registry_addr: AssignedValue<F>,
    bls_pubkey_compendium_addr: AssignedValue<F>,
    operator_to_g1_pubkey_x_slot: AssignedValue<F>,
    operator_to_g1_pubkey_y_slot: AssignedValue<F>,
    quorum_g1_apk_x_slot: AssignedValue<F>,
    quorum_g1_apk_y_slot: AssignedValue<F>,
    task_created_block: AssignedValue<F>,
}

impl RawCircuitInput<Fr, MyCircuitVirtualInput<Fr>> for MyCircuitInput {
    fn default() -> Self {
        MyCircuitInput {
            task_response_digest_g2coords: [0; 128],
            agg_sig_g2coords: [0; 128],
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


pub fn encode_slot_to_lo_hi(slot: &Fr) -> (Fr, Fr) {
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

        let gate = GateChip::<Fr>::new();

        let task_response_digest_g2coords = G2Affine::from_raw_bytes(&inputs.task_response_digest_g2coords).unwrap();
        let agg_sig_g2coords = G2Affine::from_raw_bytes(&inputs.agg_sig_g2coords).unwrap();

        let slot_lo_hi = encode_slot_to_lo_hi(inputs.operator_to_g1_pubkey_x_slot.value());
        let slot_lo_loaded = builder.base.borrow_mut().main(0).load_witness(slot_lo_hi.0);
        let slot_hi_loaded = builder.base.borrow_mut().main(0).load_witness(slot_lo_hi.1);
        
        let storage_slot_subquery = AssignedStorageSubquery {
            block_number: inputs.task_created_block,
            addr: inputs.bls_pubkey_registry_addr,
            slot: AssignedHiLo {
                hi: slot_hi_loaded,
                lo: slot_lo_loaded
            },
        };

        let subquery = AssignedHeaderSubquery {
            block_number,
            field_idx,
        };
        let timestamp = subquery_caller.call(builder.base.borrow_mut().main(0), subquery);
        callback.push(timestamp);
        dbg!(timestamp.lo().value());
    }
}

#[test]
pub fn test_keygen() {
    dotenv().ok();
    let circuit = MyCircuit;
    let params = BaseCircuitParams {
        k: 12,
        num_advice_per_phase: vec![4, 0, 0],
        num_lookup_advice_per_phase: vec![1, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(11),
    };
    let client = Provider::<Http>::try_from(env::var("PROVIDER_URI").unwrap()).unwrap();
    keygen(circuit, client, params, None);
}

#[test]
pub fn test_mock() {
    dotenv().ok();
    let circuit = MyCircuit;
    let params = BaseCircuitParams {
        k: 12,
        num_advice_per_phase: vec![4, 0, 0],
        num_lookup_advice_per_phase: vec![1, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(11),
    };
    let client = Provider::<Http>::try_from(env::var("PROVIDER_URI").unwrap()).unwrap();
    mock(circuit, client, params, None);
}

#[test]
pub fn test_prove() {
    dotenv().ok();
    let circuit = MyCircuit;
    let params = BaseCircuitParams {
        k: 12,
        num_advice_per_phase: vec![4, 0, 0],
        num_lookup_advice_per_phase: vec![1, 0, 0],
        num_fixed: 1,
        num_instance_columns: 1,
        lookup_bits: Some(11),
    };
    let client = Provider::<Http>::try_from(env::var("PROVIDER_URI").unwrap()).unwrap();
    let pk = keygen(circuit.clone(), client.clone(), params.clone(), None);
    prove(circuit, client, params, None, pk);
}
