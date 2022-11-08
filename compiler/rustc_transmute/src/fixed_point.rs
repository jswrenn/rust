use std::collections::{BTreeSet, HashMap};

use crate::{layout::Ref, maybe_transmutable::Quantifier, Answer, IfTransmutable};

// struct Equation
// enum FA { Yes, No, Maybe }
// Equations :: Map Variable  -> Answer
// mapping = {v:Maybe for v in keys(Equations)} ; Variable -> FA
// worklist = {v for v in keys(Equations)} ; start off at all the variables
// while let Some(v) = worklist.pop() {
//  simp = simplify(Equations[v], mapping)
//  if (simp is either 'Yes' or 'No')
//      mapping[v] = Equations[v]
//      for every equation that mentions v:
//          worklist.push(equation)
//
// }
// mapping = {v:Yes if x is Maybe else x for (v,x) in mapping}
//
// simplify(equation, mapping):
//  match equation:
//      Yes => Yes
//      No => No
//      IfTransmutable(v) if mapping[v] is Yes | No => mapping[v]
//      Any<vs> => "recurse and if they're all concrete, actually do the Or and return Yes or No"
//      All<vs> => "recurse and if they're all concrete, actually do the And and return Yes or No"
//  struct X(u8, &Y); struct Y(u8, &X);
// X=>Y = Y=>X
// Y=>X = X=>Y
//

pub fn solve<R: Ref>(trans: IfTransmutable<R>, ans: Answer<R>) -> Answer<R> {
    let mut equations = HashMap::from([(trans, ans)]);
    let mut mappings = HashMap::new();
    // TODO: Initialize with all of the transmutes from the initial equation.
    let mut worklist = BTreeSet::new();

    while let Some(trans) = worklist.pop_first() {
        // TODO: Can this lookup ever fail?
        let ans = equations.get_mut(&trans).unwrap().simplify(&mappings);
        if matches!(ans, Answer::Yes | Answer::No(_)) {
            mappings.insert(trans, *ans);
            for eq in every_equation_that_mentions_trans {
                worklist.push(eq);
            }
        }
    }

    // This `unwrap` is safe because we initialized the map at the beginning
    // with `trans`, and never removed any keys until now.
    equations.remove(&trans).unwrap()
}

impl<R: Ref> Answer<R> {
    fn simplify(&mut self, mappings: &HashMap<IfTransmutable<R>, Answer<R>>) -> &mut Self {
        let (rhss, quant) = match self {
            Answer::IfTransmutable(pred) if let Some(ans @ (Answer::Yes | Answer::No(_))) = mappings.get(pred) => {
                *self = ans.clone();
                return self
            }
            Answer::IfTransmutable(_) | Answer::Yes | Answer::No(_) => return self,
            Answer::IfAll(rhss) => (rhss, Quantifier::ForAll),
            Answer::IfAny(rhss) => (rhss, Quantifier::ThereExists),
        };

        match quant.apply(rhss.iter_mut().map(|rhs| &*rhs.simplify(mappings)).cloned()) {
            ans @ (Answer::Yes | Answer::No(_)) => *self = ans,
            Answer::IfTransmutable(_) | Answer::IfAll(_) | Answer::IfAny(_) => {}
        }

        self
    }
}
