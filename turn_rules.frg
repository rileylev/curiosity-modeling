open "cm.sigs.frg"

// Play begins with the dealer and continues counterclockwise.
// A turn begins with a player attempting to match one of the cards lying
// face-up on the table with a card of the same month in their hand.
// If there are two cards of the same month already on the table, the
// player may select one of them. If the player has no cards matching
// the cards on the table, the player discards a card to the table.

pred same_month[x,y: Card] { x.month = y.month }

// TODO: I think there's a way to rewrite these using just relational algebra
// like a projection and intersect or something
pred match[hand, table: set Card, in_hand, in_table: Card]{
  hand[in_hand]
  table[in_table]
  same_month[in_hand,in_table]
}
pred no_match[hand, table: set Card] {
  all in_hand: hand, in_table: table | {
    !same_month[in_hand, in_table]
  }
}

pred move[K: Card, from_pre, from_post, to_pre, to_post: set Card]{
  from_post = from_pre - K
  to_post = to_pre + K
}

// I want to write as much of it independent of time as possible
// because it will make it easier to test and save other
// headaches
pred step2[hand, table, hand_after, discard, table_after: set Card,
           hand_match, table_match: Card]{
  some in_hand, in_table: Card | {
    match[hand, table,in_hand,in_table]
    hand_after = hand
    table_after = table
    no discard
  } or {
    no_match[hand,table]
    move[discard,hand,table,hand_after,table_after]
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
  some pre_deck[flipped, pre]
  post_deck = pre_deck - flipped
}
pred step3_flipping[flipped, table_match: Card,
                    pre_table, post_table, pre_deck, post_deck: set Card]{
  draw[flipped, pre_deck, post_deck]
  some K: table | {
    same_month[K,flipped]
    table_match = K
    pre_table = post_table
  } or {
    no table_match
    post_table = pre_table + flipped
  }
}

// If the card drawn from the top of the draw pile in step 3 matches the two
// cards matched in step 2, the three cards remain on the table. This is
// known as ppeok (뻑; ppeog). The three cards remain until a player collects
// them using the fourth card of the same month.
pred is_ppeok[x,y,z: Card]{ same_month[x,y] && same_month[y,z] }
pred is_pi[flipped,discarded: Card]{ same_month[flipped, discarded] }
pred is_ttadak[played, flipped: Card, table: set Card] {
  some disj x,y : table | {
    same_month[x,played]
    same_month[y,played]
    same_month[played,flipped]
  }
}


// If a player draws a card that matches the card discarded in step 2, the
// player collects both cards as well as one junk card (pi) from each
// opponent's stock pile. This is known as chok.
//
// If a player plays a card in step 2 for which two matching cards are
// already on the table, and then draws the fourth matching card from the
// draw pile in step 3, the player collects all four cards as well as one junk
// card (pi) from each opponent's stock pile. This is known as ttadak.[7]
// TODO: what's a stock pile???
//
// The object of the game is to create scoring combinations to accumulate
// points up to a score of either three (for three players) or seven
// (for two players), at which point a "Go" or a "Stop" must be called.
//
// A game that ends with neither a "Go" nor "Stop" call is called a Nagari
// game (나가리; nagali). The dealer and play order of the next game remain
// the same as with the Nagari game, and when the game ends, the loser owes
// the winner double money.
