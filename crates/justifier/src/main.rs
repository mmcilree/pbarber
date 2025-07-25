use pbarber_lib::{
    rup,
    statements::{ConstraintStatement, Direction, Label, PolStatement, ProofRule},
    terms::{Flag, LinearSum, Var, WeightedSum},
};

fn main() {
    // let mut sum = LinearSum::new();

    let x = Var::with_id(0);
    // let y = Var::with_id(1);
    // let z = x.times(-1).add(3);
    // let f = Flag::with_id(0);

    // let xge3 = x.ge(3);
    // let term = 3 * x.ge(3);
    // let mut sum = 2 * x.ge(4) + 1 * !y.eq(2);

    // sum += 3 * !x.ge(3);
    // sum += 1 * f + 3 * z;
    // let con = sum.ge(5);
    // println!("{:?}", con);

    let label1 = Label::from("another_label");

    let mut pol = PolStatement::with_label("my_label".into());
    pol = pol + 3 * x.ge(3).def_label() + 4 * label1;
    print!("{:?}", pol);

    let rup = rup!((3 * x.ge(3) + 4 * x.lt(2)).ge(3)).with_label("my_label".into());
}
