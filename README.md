# Go-Stop
[Go-Stop](https://en.wikipedia.org/wiki/Go-Stop) is a Korean card game played with Hanafuda (or _Hwatu_ as they are known in Korean) cards. Hwatu cards have a Suit (Bright, Animal, Ribbon, Junk/Double Junk) and a Month (Jan-Dec). The cards are not necessarily unique. The gameplay involves drawing cards from the deck and matching cards by Suit from the player's hand and the table. It is generally played with 2-3 players, and we model the three player version.

## Features
Even though our model simplifies Go-Stop, it uses the full set of cards as real Go-Stop and preserves the core gameplay loop: that is, our model goes through each step taken in a real Go-Stop game. We merely cut out special cases for scoring which are added on top of the base rule such as Godori scoring. If you are interested in what some of these special rules look like, the `extensions.frg` file has some instances of special rules we wrote, but never quite got to integrating into our model.

## Design
We manually made individual sigs for Months rather than using integers, since we found this easier to enforce valid values with. Instead of 5 Suites, we actually have

We use a trace-based model. Therefore, we start with an `initial` predicate which ensures that all cards are in the deck and NOT in the hands of players or on the table. Then, we use the `nextTurn` predicate to define the transition between turns.

Because we are modeling something stateful and were uncertain on what the final model of state would look like, a lot of the 
core rules were modeled in a "purely functional" time-agnostic way. This makes calling the predicates more
complicated but it kept them insulated from uncertainty in the design, which paid off when we changed the implementation of state. 

The rules for the steps taken on each turn are split into individual predicates that correspond to the steps listed in the Wikipedia page. To keep them state-agnostic, anything that must change is passed in as before/after pairs, for example `step2` "changes" the hand and the table and so takes in pairs of each. The potential downside to this design choice is using existentially quantified variables to wire together each step might put undue stress on the solver. And predicate signatures get extremely long, but I'd argue this reflects the incidental complexity in the game's rules. 

We also considered several different strategies of modeling the game. To list a few that we considered but ultimately didn't use,
- all state-related Sigs (e.g. Deck, Player, Table) have pfunc field from an `Hour` sig to `set Card`.

Having a separate `Hour` sig became too difficult to manage

- inductive model

It failed to adequately represent events like winning. Furthermore, the state of a go-stop game is too complex to derive a general property from.

- Card Sig is `set Month -> Suit -> Owner`, where Owner can be `Player`, `Table`, or `Deck`. Essentially, we treat the set of Cards as a grid with row Month and col Suit, and a cell holding information about who owns that card

The existence of duplicate cards made keeping track of all locations of the Card too complex

## Usage
Because of the large size of the model, it may feel overwhelming when you first see the sterling visualizer output. We recommend making as many fields as possible into properties, as that greatly reduces the clutter. Seong-Heon personally runs the graph view with all fields of `Turn` made into properties instead of arrow & nodes.
Furthermore, make sure to enforce a rather tight bound on how many turns you want in your output. Without this, model will take very long to run. 

## Testing
- cards
The cards test ensures two things: it is only possible to make 48 cards with the given predicates and the cards are given appropriate suits and months. Technically, it would be possible to have 48 tests that check for the existence of each card, but we find this to be a more generalizable solution. Because most of the predicates that compose `cardWellformed` are fairly rudimentary (e.g. each month has four cards), we just test the `cardWellformed` predicate. It relies heavily on asserts.

- turn rules
Each step in a turn's predicate was unit tested independently. We had to approximate higher-order quantification for some of the tests in order to create sets of cards for example to pass to the predicates under test. Most of the tests proved the predicate had a certain property by showing finding a counterexample is unsatisfiable. 

- score
Because the scoring system was simplified a fair amount, the tests here are also quite simple. They check that winning is triggered for appropriate conditions

- domain area
So far we haven't had a chance to do much unfortunately.

## Challenges
One large hurdle we encountered during the project is performance. Forge struggled working with a total of 48 Cards (4 for each Month) and thus needed some manual intervention. We had to manually adjust the bitwidth and specify the number of Cards in advance through `for exactly 48 Card`. Of course, before adding the `for exactly 48 Card` constraint, we wanted to sure that our model would have ended up with only 48 cards anyway. So, we have a test for `cardWellformed` that asserts that `cardWellformed` is sufficient for having exactly 48 cards (this test is run without `for exactly 48 Card`). Having proven this, we run subsequent tests with `for exactly 48 Card` to optimize the solver.

This got worse after adding in all the rules for each turn, but relaxing the `cardWellformed`rules let us get output in reasonable time

The rules of Gostop are also irregular and complicated, so stating them formally is tricky. And they're a bit ambiguous. 

We also run into some limitations of Forge/first-order logic. We needed to approximate higher-order quantification in order to work with sets of cards (hand, deck) and arrays of sets of cards (each player's hand or stockpile). 
