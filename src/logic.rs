use crate::UnitResult;
use crate::phrase::*;

pub fn instantiate(quantification: Phrase, term: Phrase) -> Result {
    if quantification.get_kind() != Quantify {
        Err(format!(
            "instantation requires a quantification, got {quantification}"
        ))?
    }
    let (variable, formula) = quantification.get_children().unwrap_two();
    let new = formula.clone().substitute(variable.clone(), term)?;
    let new = make_imply(quantification, new)?;
    new.assert_axiom(Name("instantiate"))
}

pub fn distribute(quantification: Phrase) -> Result {
    if quantification.get_kind() != Quantify {
        Err(format!(
            "distribute requires a quantification, got {quantification}"
        ))?
    }
    let (variable, formula) = quantification.get_children().unwrap_two();
    if formula.get_kind() != Imply {
        Err(format!(
            "distribute requires an implication as the formula of the quantification, got {formula}"
        ))?
    }
    let (left, right) = formula.get_children().unwrap_two();
    let variable = variable.clone();
    let left = left.clone();
    let right = right.clone();
    let new = make_imply(
        quantification,
        make_imply(
            make_quantify(variable.clone(), left)?,
            make_quantify(variable, right)?,
        )?,
    )?;
    new.assert_axiom(Name("distribute quantification"))
}

pub fn axioms() -> UnitResult {
    let var_a = make_logic_variable("'A".into())?;
    let var_b = make_logic_variable("'B".into())?;
    let var_c = make_logic_variable("'C".into())?;

    make_imply(var_a.clone(), make_imply(var_b.clone(), var_a.clone())?)?
        .assert_axiom(Name("ignore"))?;

    make_imply(
        make_imply(var_a.clone(), make_imply(var_b.clone(), var_c.clone())?)?,
        make_imply(
            make_imply(var_a.clone(), var_b.clone())?,
            make_imply(var_a.clone(), var_c.clone())?,
        )?,
    )?
    .assert_axiom(Name("distribute implication"))?;

    make_imply(
        make_imply(make_not(var_a.clone())?, make_not(var_b.clone())?)?,
        make_imply(var_b.clone(), var_a.clone())?,
    )?
    .assert_axiom(Name("contrapose"))?;

    Ok(())
}
