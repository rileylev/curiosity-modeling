#lang forge

open "sigs.frg"

// Play begins with the dealer and continues counterclockwise.
// A turn begins with a player attempting to match one of the cards lying
// face-up on the table with a card of the same month in their hand.
// If there are two cards of the same month already on the table, the
// player may select one of them. If the player has no cards matching
// the cards on the table, the player discards a card to the table.

pred same_month[x,y: Card] { x.month = y.month }

pred match[hand, table: set Card, in_hand, in_table: Card]{
  in_hand in hand
  in_table in table
  same_month[in_hand,in_table]
}
pred no_match[hand, table: set Card] {
  all in_hand: hand, in_table: table | {
    !same_month[in_hand, in_table]
  }
}

pred move[K: Card, from_pre, from_post, to_pre, to_post: set Card]{
  K in from_pre
  from_post = from_pre - K
  to_post = to_pre + K
}

// I want to write as much of it independent of time as possible
// because it will make it easier to test and save other
// headaches
pred step2[hand, hand_after, table, table_after: set Card,
           hand_match, table_match, discard: Card]{
  some in_hand, in_table: Card | {
    match[hand, table,in_hand,in_table]
    hand_after = hand
    table_after = table
    no discard
  } or {
    no_match[hand,table]
    move[discard,hand,hand_after,table,table_after]
    no hand_match
    no table_match
  }
}

// The turn continues with the player flipping over the top card from the
// draw pile and looking for a card of the same month on the table. If
// the player finds a matching card on the table, the player collects both
// cards along with the cards matched in step 2. Otherwise, the drawn card
// is added to the table.
pred draw[drawn: Card, pre_deck: set Card, post_deck: set Card]{
  drawn in pre_deck
  post_deck = pre_deck - drawn
}
pred step3_flipping[flipped, table_match: Card,
                    pre_table, post_table, pre_deck, post_deck: set Card]{
  draw[flipped, pre_deck, post_deck]
  some K: pre_table | {
    same_month[K,flipped]
    table_match = K
    post_table = pre_table - table_match
  } or {
    no table_match
    post_table = pre_table + flipped
  }
}

// TODO: is this an exception?
// If the card drawn from the top of the draw pile in step 3 matches the two
// cards matched in step 2, the three cards remain on the table. This is
// known as ppeok (뻑; ppeog). The three cards remain until a player collects
// them using the fourth card of the same month.
pred same_month3[x,y,z: Card]{ same_month[x,y] && same_month[y,z] }

pred ppeok[flipped, matched1, matched2: Card, pre_hand,
           post_hand, pre_table, post_table: set Card] {
  {
    same_month3[flipped,matched1, matched2]
    post_table = pre_table + flipped + matched1 + matched2
  } or {
    post_hand = pre_hand + flipped + matched1 + matched2
    post_table = pre_table - flipped - matched1 -matched2
  }
}

// If a player draws a card that matches the card discarded in step 2, the
// player collects both cards as well as one junk card (pi) from each
// opponent's stock pile. This is known as chok.
//TODO: junk from stock piles??????
pred is_junk[card: Card] {
  card.suit in (Junk1 +Junk2 + DoubleJunk)
}
pred has_a_junk[pile: set Card] {
  some j: pile | {
    is_junk[j]
  }
}
pred steal1junk[junks: set Card, pre_piles, post_piles: set Int -> Card] {
  all j: junks | {
    is_junk[j]
    some i: Int | {
      j = pre_piles[i] - post_piles[i]
    }
  }
  all i: Int | {
    // Is stealing mandatory?
    has_a_junk[pre_piles[i]] => (post_piles[i] != pre_piles[i])
    post_piles[i] in pre_piles[i]
    (pre_piles[i] - post_piles[i]) in junks
  }
}
pred no_steal[pre_piles, post_piles: set Int -> Card] {
  steal1junk[none, pre_piles, post_piles]
}

pred pi[flipped, discarded: Card,
        pre_hand, post_hand, pre_table, post_table: set Card,
        pre_piles, post_piles: set Int-> Card] {
  {
    same_month[flipped, discarded]
    some wjunks : CardSetWrapper | {
      steal1junk[wjunks.cardset, pre_piles, post_piles]
      post_hand = wjunks.cardset + pre_hand + flipped + discarded
    }
    post_table = pre_table - flipped - discarded
  } or {
    !same_month[flipped, discarded]
    no_steal[pre_piles, post_piles]
    post_hand  = pre_hand
    post_table = pre_table
  }
}

// If a player plays a card in step 2 for which two matching cards are
// already on the table, and then draws the fourth matching card from the
// draw pile in step 3, the player collects all four cards as well as one junk
// card (pi) from each opponent's stock pile. This is known as ttadak.[7]
// TODO: what's a stock pile???
pred same4months[x,y,played,flipped: Card]{
  same_month[x,played]
  same_month[y,played]
  same_month[played,flipped]
}
pred ttadak[played, flipped: Card,
            pre_hand, post_hand, pre_table,post_table: set Card,
            pre_piles, post_piles: set Int -> Card] {
  some disj x,y : pre_table | {
    same4months[x,y,played, flipped]
    some wjunks: CardSetWrapper | {
      steal1junk[wjunks.cardset, pre_piles, post_piles]
      post_hand = pre_hand + wjunks.cardset + x + y + played + flipped
    }
    post_table = pre_table - x -y -played -flipped
  } or {
    no disj x,y : pre_table | {same4months[x,y,played,flipped]}
    no_steal[pre_piles, post_piles]
    pre_hand = post_hand
    pre_table = post_table
  }
}

// The object of the game is to create scoring combinations to accumulate
// points up to a score of either three (for three players) or seven
// (for two players), at which point a "Go" or a "Stop" must be called.
//
// A game that ends with neither a "Go" nor "Stop" call is called a Nagari
// game (나가리; nagali). The dealer and play order of the next game remain
// the same as with the Nagari game, and when the game ends, the loser owes
// the winner double money.
