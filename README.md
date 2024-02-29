# Go-Stop
[Go-Stop](https://en.wikipedia.org/wiki/Go-Stop) is a Korean card game played with Hanafuda (or _Hwatu_ as they are known in Korean) cards. Hwatu cards have a Suit (Bright, Animal, Ribbon, Junk/Double Junk) and a Month (Jan-Dec). The cards are not necessarily unique. The gameplay involves drawing cards from the deck and matching cards by Suit from the player's hand and the table. It is generally played with 2-3 players, and we model the three player version.

## Features
Even though our model simplifies Go-Stop, it uses the full set of cards as real Go-Stop and preserves the core gameplay loop: that is, our model goes through each step taken in a real Go-Stop game. We merely cut out special cases for scoring which are added on top of the base rule such as Godori scoring. If you are interested in what some of these special rules look like, the `extensions.frg` file has some instances of special rules we wrote, but never quite got to integrating into our model.

## Challenges
One large hurdle we encountered during the project is performance. Forge struggled working with a total of 48 Cards (4 for each Month) and thus needed some manual intervention. We had to manually adjust the bitwidth and specify the number of Cards in advance through `for exactly 48 Card`. Of course, before adding the `for exactly 48 Card` constraint, we wanted to sure that our model would have ended up with only 48 cards anyway. So, we have a test for `cardWellformed` that asserts that `cardWellformed` is sufficient for having exactly 48 cards (this test is run without `for exactly 48 Card`). Having proven this, we run subsequent tests with `for exactly 48 Card` to optimize the solver.

## Design
We use a trace-based model.
We also considered several different strategies of modeling the game. To list a few that we considered but ultimately didn't use,
- all state-related Sigs (e.g. Deck, Player, Table) have pfunc field from an `Hour` sig to `set Card`.

Having a separate `Hour` sig became too difficult to manage

- inductive model

It also failed to adequately represent events like winning. Furthermore, the state of a go-stop game is too complex to derive a general property from.

- Card Sig is `set Month -> Suit -> Owner`, where Owner can be `Player`, `Table`, or `Deck`. Essentially, we treat the set of Cards as a grid with row Month and col Suit, and a cell holding information about who owns that card

The existence of duplicate cards made keeping track of all locations of the Card too complex