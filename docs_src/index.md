---
title: On a density conjecture about unit fractions
---
# What is it about?

The goal of this project is to formalize the main result of the preprint
['On a density conjecture about unit fractions'](https://arxiv.org/abs/2112.03726)
using the [Lean theorem prover](https://leanprover.github.io/), 
mainly developed at [Microsoft Research](https://www.microsoft.com/en-us/research/) 
by [Leonardo de Moura](https://leodemoura.github.io/).
This project structure is adapted from the infrastructure created by Patrick Massot 
for the [Sphere Eversion project](https://github.com/leanprover-community/sphere-eversion).


More precisely we will prove that, any dense set of integers contains
distinct integers whose reciprocals sum to 1. (This generalises a colouring
result of Croot, and resolves an old open problem of Erdős and Graham.) For further
details, precise statements, context, and so on, we refer to the preprint itself.

### Exploring and helping

The best way to get started is to read the blueprint introduction,
either in [pdf](blueprint.pdf) or [online](blueprint/sect0001.html).
Then have a look at the [dependency graph](blueprint/dep_graph.html),
paying special attention to blue items. 
Blue items are items that are ready to be formalized because their
dependencies are formalized.
For lemmas, a blue border means the statement is ready for formalization,
and a blue background means the proof is ready for formalization.

If you are interested in contributing, or have any questions about the project,
please email bloom@maths.ox.ac.uk. 
