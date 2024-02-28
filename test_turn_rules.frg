#lang forge

open "cm.sigs.frg"
open "turn_rules.frg"

test suite for match {
  test expect { same_month_singletons_must_match: {
    some x,y : Card | {
      same_month[x,y]
      !( some a,b: Card | { match[x,y,a,b] })
    }
  } is unsat}
  test expect { different_month_singletons_must_not_match: {
    some x,y : Card | {
      !same_month[x,y]
      some a,b: Card | { match[x,y,a,b] }
    }
  } is unsat}
}
test suite for no_match {
  test expect { same_month_singletons_must_not_no_match: {
    some x,y : Card | {
      same_month[x,y]
      no_match[x,y]
    }
  } is unsat}
  test expect { different_month_singletons_must_no_match: {
    some x,y : Card | {
      !same_month[x,y]
      !no_match[x,y]
    }
  } is unsat}
}

test suite for move {
  test expect { moving_a_singleton_to_empty_results_in_empty_and_singleton: {
    some x : Card | {
      !move[x,x, none, none, x]
    }}
    is unsat
  }
}
