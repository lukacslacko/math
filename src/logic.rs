use crate::phrase::*;

pub fn instantiate(quantification: Phrase, term: Phrase) -> Result {
    if quantification.get_kind() != Quantify {
        Err("instantiate")?
    }
    let (variable, formula) = quantification.get_children().unwrap_two();
    let new = formula.clone().substitute(variable.clone(), term)?;
    let new = make_quantify(quantification, new)?;
    new.assert_axiom();
    new
}

pub fn distribute(quantification: Phrase) -> Result {
    if quantification.get_kind() != Quantify {
        Err("distribute not quantification")?
    }
    let (variable, formula) = quantification.get_children().unwrap_two();
    if formula.get_kind() != Imply {
        Err("distribute not implication")?
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
    new.clone().assert_axiom();
    Ok(new)
}

pub fn axioms() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let var_a = make_logic_variable("%A".to_string())?;
    let var_b = make_logic_variable("%B".to_string())?;
    let var_c = make_logic_variable("%C".to_string())?;
    make_imply(var_a.clone(), make_imply(var_b.clone(), var_a.clone())?)?
        .assert_axiom();
    make_imply(
        make_imply(var_a.clone(), make_imply(var_b.clone(), var_c.clone())?)?,
        make_imply(
            make_imply(var_a.clone(), var_b.clone())?,
            make_imply(var_a.clone(), var_c.clone())?,
        )?,
    )?
    .assert_axiom();
    make_imply(
        make_imply(make_not(var_a.clone())?, make_not(var_b.clone())?)?,
        make_imply(var_b.clone(), var_a.clone())?,
    )?
    .assert_axiom();
    Ok(())
}
