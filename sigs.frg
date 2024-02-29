#lang forge

// at its most abstract, a card is just a tuple
abstract sig Suit {}
abstract sig Month {}

one sig Bright, Animal, Ribbon, Junk1, Junk2, DoubleJunk extends Suit {}
one sig Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec extends Month {}

sig Card {
  suit: one Suit,
  month: one Month
}

-- Represents the state of the game at the START of a turn
sig Turn {
    -- player ID to card mapping
    -- We _could_ hard-code this, but we wanted to leave a bit of wiggle room for future expansion
    players: set Int -> Card,
    table: set Card,
    deck: set Card,
    -- the player who WILL go
    playing: one Int
}

-- Represents an entire (or at least up to permitted turns) game loop of go-stop
-- By entire game loop, we mean up to the point where someone reaches the score threshold
one sig Game {
    firstTurn: one Turn,
    next: pfunc Turn -> Turn
}

sig CardSetWrapper {
  cardset: set Card
}
