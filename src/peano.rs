use crate::UnitResult;
use crate::phrase::*;

pub fn axioms() -> UnitResult {
    let var_x = make_numeric_variable("X".to_string())?;
    let var_y = make_numeric_variable("Y".to_string())?;
    let zero = make_numeric_constant_zero("0".to_string())?;

    make_not(make_equals(zero.clone(), make_successor(var_x.clone())?)?)?
        .assert_axiom(Name("peano 1"))?;

    make_imply(
        make_equals(
            make_successor(var_x.clone())?,
            make_successor(var_y.clone())?,
        )?,
        make_equals(var_x.clone(), var_y.clone())?,
    )?
    .assert_axiom(Name("peano 2"))?;

    make_equals(make_add(var_x.clone(), zero.clone())?, var_x.clone())?
        .assert_axiom(Name("peano 3"))?;

    make_equals(
        make_add(var_x.clone(), make_successor(var_y.clone())?)?,
        make_successor(make_add(var_x.clone(), var_y.clone())?)?,
    )?
    .assert_axiom(Name("peano 4"))?;

    make_equals(make_multiply(var_x.clone(), zero.clone())?, zero.clone())?
        .assert_axiom(Name("peano 5"))?;

    make_equals(
        make_multiply(var_x.clone(), make_successor(var_y.clone())?)?,
        make_add(make_multiply(var_x.clone(), var_y.clone())?, var_x.clone())?,
    )?
    .assert_axiom(Name("peano 6"))?;

    make_equals(var_x.clone(), var_x.clone())?
        .assert_axiom(Name("reflexivity"))?;

    Ok(())
}

pub fn induction(
    #[expect(non_snake_case)] P: Phrase,
    variable: Phrase,
) -> Result {
    if variable.get_kind() != NumericVariable {
        Err("induction")?
    }
    // P[v / 0] ⇒ (P ⇒ P[v / 𝗦(v)]) ⇒ P
    make_imply(
        P.clone().substitute(
            variable.clone(),
            make_numeric_constant_zero("0".to_string())?,
        )?,
        make_imply(
            P.clone(),
            P.substitute(variable.clone(), make_successor(variable)?)?,
        )?,
    )?
    .assert_axiom(Name("induction"))
}

pub fn eq_subs(
    #[expect(non_snake_case)] A: Phrase,
    x: Phrase,
    y: Phrase,
) -> Result {
    if !matches!(x.get_kind(), NumericVariable | NumericConstant) {
        Err("eq_subs")?
    }
    if !matches!(y.get_kind(), NumericVariable | NumericConstant) {
        Err("eq_subs")?
    }
    make_imply(
        make_equals(x.clone(), y.clone())?,
        make_imply(A.clone(), A.substitute(x, y)?)?,
    )?
    .assert_axiom(Name("indiscernibility of identicals"))
}
