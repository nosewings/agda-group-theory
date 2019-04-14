> And when Alexander saw the breadth of his domain, he wept, for there were no more worlds to conquer.

The above is a misquotation. The original passage, from Plutarch's *Moralia*, reads:

> Alexander wept when he heard Anaxarchus discourse about an infinite number of worlds, and when his friends inquired what ailed him, "Is it not worthy of tears," he said, "that, when the number of worlds is infinite, we have not yet become lords of a single one?"

# Where's the good stuff?

Look in `Algebra.Group.Lagrange`. The proof term `lagrange` of Lagrange's theorem is at the bottom of the file.

Note that even the type of the theorem already contains a nontrivial assumption: the definition of `size-of`. There are multiple definitions of finiteness in MLTT; indeed, there are multiple *non-equivalent* ways to define finiteness. The definition under consideration here is first defined in `Finite.UList.Core`.

# Where's the bad stuff?

Everything under `Base` is pretty boring, and not all of it is strictly necessary. `List.One` *is* necessary, but it feels like there should be a better way to accomplish it.

Everything related to finiteness is unfortunate. Especially notable: if `B` is finite and there is an injection from `A` to `B`, we can't prove that `A` is finite.

# Okay, where's the *really* bad stuff?

Set-partitions are a disaster. In retrospect, this is unsurprising: set-partitions are an inherently set-theoretical concept. But it is hard to imagine how to prove Lagrange's theorem without them. This is a real problem for MLTT: extremely basic combinatorics takes a ridiculous amount of work. Indeed, all the real work in this "proof of Lagrange's theorem" went into a proof that (essentially) the sum of the sizes of the constituents of a set-partition is equal to the size of the original set. The proof term for that fact is in `Finite.Partition`; but if you want to see some truly horrifying stuff, check out `Finite.Partition.Pseudo`. Pay particular attention to the type of `stupid-lemma` (and the accompanying `stupid-lemma-lemma`). `Finite.Partition.Core`, while intimidating at first, is comparatively quite nice. Also check out `Finite.UList.Partition`.
