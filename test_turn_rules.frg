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

sig CardSetWrapper {
  cardset: set Card
}

// these tests are weaker because proving the negation unsat
// is a little annoying since there's multiple valid choices
// for matches or discards
test suite for step2 {
  test expect {
    can_discard_if_you_dont_have_a_match: {
      some hand, table: CardSetWrapper, discard: Card | {
        no_match[hand.cardset, table.cardset]
        step2[hand.cardset, hand.cardset-discard, table.cardset,
               table.cardset+discard, none, none, discard]
      }
    }
    is sat
  }

  test expect {
    can_keep_if_you_do_have_a_match: {
      some hand, table: CardSetWrapper, in_hand,in_table: Card | {
        match[hand.cardset, table.cardset, in_hand, in_table]
        step2[hand.cardset, hand.cardset, table.cardset,
               table.cardset, in_hand, in_table, none]
      }
    }
    is sat
  }
}

test suite for draw{
  test expect {
    drawing_removes_a_card_from_the_deck: {
      some pre_deck, post_deck: CardSetWrapper, card: Card | {
        draw[card, pre_deck, post_deck]
        !(card in post_deck)
      }
    } is unsat
  }
}
