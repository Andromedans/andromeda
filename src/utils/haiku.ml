(* courtesy of http://www.cl.cam.ac.uk/research/hvg/haiku.html *)
let haikus = [
  "    Theorem proving sucks
    I don't know why we bother
    What a waste of time.

              - Michael Norrish
";
"    The sun spills darkness
    A dog howls after midnight
    Goals remain unsolved.

              - Chris Owens
";
"    Forgotten lemma?
    Shameless optimist!  Use HOL,
    then you know it's right.

              - Mark Staples
";
"    crazy semantics
    embedded in a prover
    raises exception

              - Daryl Stewart
";
"    No more goals remain
    Out the door, down the dark road
    Unknowing city.

              - Konrad Slind
";
"    It's blatantly clear
    You stupid machine, that what
    I tell you is true

              - Michael Norrish
";
"    I know not a thing
    to do with theorem proving -
    somehow, life goes on.

              - Kona Macphee
";
"    Cherry blossoms fade
    Their beauty is gossamer
    Theorems are blossoms

              - Phil Windley
";
"    HOL words frighten me;
    Axiomatization,
    In particular.

              - Robert Beers
";
"    Theorem proving and
    sanity; Oh, my! What a
    delicate balance

              - Victor Carreno
";
"    This chip is correct?
    Well no, but it's verified
    Which means what? (you know)

              - Evan Cohn
";
"    What is, may be seen
    Suck and see, the answer is,
    But may not be, known

              - Gerard M Blair
";
"    In the cool morning
    A man simplifies, a goal
    A theorem is born

              - Don Syme
";
"    Axiom of choice
    Hilbert's epsilon serene
    I construct no more

              - Don Syme
";
"    Co-inductive set
    I do not transgress your rules
    You are well-founded

              - Don Syme
";
"    Formalization:
    dense phrasing... obfuscation
    is side benefit.

              - Trent Larson
";
"    In finding the truth
    Found a tool to demonstrate false
    and so what now ?

              - Dirk Van Heule
";
"    Isabelle doesn't
    understand me.  I don't speak
    her meta-language.

              - Claire Quigley
";
"    Original goal.
    Multiple nested lemmas;
    tangled tree of truth.

              - Peter Homeier
";
"    Discouraged by haiku,
    I decide to avoid it:
    Isabelle's too hard.

              - Keith Wansbrough
";
"    Hah!  A proof of False.
    Your axioms are bogus.
    Go back to square one.

              - Larry Paulson
";
"    Fools seek certain truth.
    That precious pearl is hidden!
    Nothing can be proved.

              - Larry Paulson
";
"    another failed proof
    frustration grows as a tree
    blame it on hardware

              - Isua Eliazar
";
"    I'm no good at this.
    I proved everything is false.
    Surely some mistake?

              - Silas S Brown
";
"    Meson search level........
    Meson search level........I think
    Its time for coffee.

              - Hugh Anderson
";
"    Don't seek refuge here.
    Your proof attempts are hopeless.
    Use Otter instead.

              - Bill McCune
";
]

let () = Random.self_init ()
let choose () = List.nth haikus (Random.int (List.length haikus))
