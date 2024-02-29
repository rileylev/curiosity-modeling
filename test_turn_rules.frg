#lang forge

open "sigs.frg"
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

sig MaybeCard {
  maybecard: lone Card
}

test suite for step3_flipping{
  test expect{
    a_card_must_be_removed_from_the_deck:{
      some F: Card, T:MaybeCard, PreT, PostT, PreD, PostD: CardSetWrapper | {
        step3_flipping[F,T.maybecard, PreT.cardset, PostT.cardset,
                       PreD.cardset, PostD.cardset]
        F in PostD.cardset
      }
    } is unsat
  }
  test expect {
    a_card_must_be_added_to_the_table_if_you_dont_flip_a_match:{
      some F: Card, PreT, PostT, PreD, PostD: CardSetWrapper | {
        step3_flipping[F,none, PreT.cardset, PostT.cardset,
                       PreD.cardset, PostD.cardset]
        !(F in PostT.cardset)
      }
    } is unsat
  }
}

test suite for is_junk {
  test expect {
    junk_is_junk: {
      some c: Card {
        c.suit = Junk1 or c.suit = Junk2
        !is_junk[c]
      }
    } is unsat
  }
  test expect {
    double_junk_is_junk: {
      some c: Card {
        c.suit = DoubleJunk
        !is_junk[c]
      }
    } is unsat
  }
  test expect {
    nothing_else_is_junk: {
      some c: Card {
        c.suit != DoubleJunk
        c.suit != Junk1
        c.suit != Junk2
        is_junk[c]
      }
    } is unsat
  }
}

sig CardSetArray {
  cardsetarray: set Int -> Card
}

test suite for steal1junk{
  test expect{
    stealing_empty_gives_empty:{
      some J: CardSetWrapper | {
        // none is the wrong thing to pass in
        steal1junk[J.cardset, Int -> none, Int -> none]
        some J.cardset
      }
    } is unsat
  }
  test expect{
    only_steal_junk: {
      some J :CardSetWrapper,X,Y: CardSetArray | {
        steal1junk[J.cardset,X.cardsetarray,Y.cardsetarray]
        some j: J.cardset | {!is_junk[j]}
      }
    } is unsat
  }
}
test suite for no_steal {
  test expect{
    piles_stay_the_same: {
      some x,y : CardSetArray {
        no_steal[x.cardsetarray,y.cardsetarray]
        x.cardsetarray!=y.cardsetarray // relation equality is pointwise equality
      }
    } is unsat
  }
}
