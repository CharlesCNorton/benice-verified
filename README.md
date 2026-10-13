# Convergence to Resource Preservation in Delayed Elimination Games

A Rocq development, `benice_verified.v`, of the following claim. An agent acts
on the resources of the world at a position in space. Other agents, the judges,
may observe the act and eliminate the agent. Signals travel at a finite speed,
so a judge at distance d sees the act after d / c and its response arrives
after 2 d / c. An agent planning over a horizon T is therefore exposed to the
judges within distance c T / 2, and that set grows with the cube of the
horizon. A destructive act is a signal; a preserving one is not. The theorems
show that the survival of any destructive act vanishes as the horizon grows,
at an explicit rate, that an action's benefit buys it an explicit crossover
depth beyond which preservation wins, that the destructiveness of any optimal
action is bounded by a quantity falling like 1 / T, and that on any finite menu
every optimal action is eventually preserving. They also show where the claim
stops: with any positive rate of time preference the survival of every action
stays above a positive floor at every depth, and without independence of the
judges it need not decay at all. A final section treats the judges as players,
derives their punishment rule from their own exposure to judges, and shows that
the asymmetry the agent-level theorems assume is the behaviour of deep judges.

## Model

Section 1 defines vectors in R^3 with the Euclidean norm and proves the metric
axioms, the Cauchy-Schwarz inequality, the triangle inequality and its reverse,
and the comparison between the l1 and Euclidean norms. Section 2 defines an
action as a map on the resource state and the destruction of an event as the
drop in the norm it causes, clamped at zero; scaling the state by f destroys
the fraction 1 - f of it. Section 3 builds the finite sums and products used
throughout, including the two-sided geometric sum. Section 4 fixes a speed of
light c, a lattice spacing res and a tolerance tol, defines judges, reception
times and the round trip, proves that the horizon radius is c T / 2
(`within_horizon_iff`) and that no judge's reception lies in another's causal
past (`receptions_not_timelike`), builds the lattice of potential judges within
a ball, counts it from below by the inscribed cube and from above by the
enclosing one (`judges_count_lower`, `judges_count_upper`), and bounds the
hazard sum, the sum over judges of attenuated signal per unit tolerance, from
below by a quantity linear in the radius (`hazard_lower_bound`). Attenuation is
any function bounded by one and no steeper than inverse square; the flat,
inverse-linear and inverse-square laws are instances.

Section 5 defines the elimination probability of a judge in the Poisson form
1 - exp(- signal / tolerance), survival as the product over the judges within
the horizon, and proves the closed form survival = exp(- offense * hazard)
(`survival_closed_form`). The offense is any non-negative functional of the
agent's options; Section 10 instantiates it with the destruction of the event.
Section 6 proves the rate: beyond the depth `T_min`, survival is at most
exp(- offense * rate * T) with `rate` explicit in c, res, tol and the
attenuation constant (`survival_upper_bound`), hence survival vanishes
(`survival_vanishes`, `survival_Un_cv`). Section 7 adds a benefit function, so
utility is benefit times survival, and proves the crossover depth
(`uniform_crossover`, `pointwise_crossover`), the bound on the offense of any
action at least as good as preservation (`optimal_offense_le`,
`optimal_offense_vanishes`), that the crossover is a genuine phase change
(`shallow_offense_wins`), and that on a finite menu every optimal action is
eventually inoffensive (`optimal_actions_are_inoffensive`). Section 8 adds time
preference: a response arriving after the round trip is weighted by
exp(- r * 2 d / c); the discounted hazard over the whole lattice is bounded,
since the lattice sum of exp(- lambda |x|) factors into three geometric sums,
so discounted survival has a positive floor at every depth
(`discounted_survival_floor`) and a sufficiently lucrative destructive action
is preferred at every depth (`discounting_blocks_convergence`). Section 9
proves that a larger horizon admits every judge of a smaller one
(`hazard_monotone`, `survival_antitone_horizon`).

Section 10 instantiates the offense with destruction and restates the results
for preserving and destructive actions: `preservation_survives`,
`destruction_survival_rate`, `destruction_survival_vanishes`,
`destruction_survival_Un_cv`, `preservation_crossover`,
`optimal_destruction_bound`, `optimal_destruction_vanishes`,
`optimal_actions_preserve`, `shallow_destruction_wins`, `deeper_never_safer`
and `time_preference_blocks_convergence`. Section 11 treats judges as players.
A judge's verdict is a best response to its payoffs (`judge_best_optimal`), and
the Poisson elimination probability is the agent's credence that the judge's
tolerance lies below the perceived offense (`elim_prob_is_tolerance_credence`).
Punishing a preserver destroys the preserver's resources, so the judge is a
destroyer under the same measure and the core theorems apply to it: its
survival vanishes with its own depth (`harsh_judge_survival_vanishes`) and deep
judges spare preservers (`deep_judges_spare_preservers`); punishing a
persistent destroyer is net-preserving once the judge's horizon exceeds the
destroyer's value over its destruction rate, and a judge whose gain exceeds its
cost punishes (`deep_judges_punish_persistent_destroyers`, `derived_asymmetry`).
Section 12 formalises couplings of the judges' decisions: the model's survival
is the joint survival of the independent coupling
(`survival_is_independent_coupling`), any coupling has joint survival at most
one minus the largest marginal (`frechet_bound`), and the perfectly dependent
coupling attains it with a survival that does not decay with the number of
judges (`all_or_nothing_survival`). Section 13 states the thesis as one theorem,
`convergence_to_resource_preservation`, and the two-level game as
`two_level_equilibrium`, and prints the axioms each depends on.

## Assumptions

The theorems are parametric in the speed of light, the lattice spacing, which
fixes the density of potential judges, their tolerance, the attenuation law, the
event position, the resource state and the benefit function. The hypotheses
that carry the thesis are stated as premises: judges respond to the destruction
of the event and not to its preservation, their decisions are independent,
elimination forfeits the whole benefit, and the agent does not discount. The
first is derived in Section 11 for judges who are themselves exposed to judges,
the second is justified in Section 4 by spacelike separation and shown
necessary in Section 12, and the fourth is shown necessary in Section 8.

## Building and checking

The development uses the Rocq Prover 9.0 with its standard library and nothing
else. It was built with the Rocq Platform 2025.08. On Windows, `build.cmd`
compiles the file and checks the compiled object with `coqchk`; on a Unix
shell, `build.sh` does the same. `_CoqProject` lists the source for
`rocq makefile -f _CoqProject -o Makefile`, after which `make` builds it.

```
coqc benice_verified.v
coqchk -silent -o -Q . "" benice_verified
```

`coqchk` reports the axioms the development rests on; they are the four axioms
of the standard library's construction of the real numbers, functional
extensionality and excluded middle. The `Print Assumptions` commands at the end
of the file report the same for the summary theorems.
