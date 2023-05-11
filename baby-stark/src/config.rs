use p3_commit::PCS;
use p3_field::{AbstractFieldExtension, PrimeField, TwoAdicField};
use p3_lde::TwoAdicLDE;

pub trait StarkConfig {
    type F: PrimeField;
    type Domain: AbstractFieldExtension<Self::F> + TwoAdicField;
    type Challenge: AbstractFieldExtension<Self::F>;
    type PCS: PCS<Self::F>;
    type LDE: TwoAdicLDE<Self::F, Self::Domain>;
}
