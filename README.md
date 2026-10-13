# Convergence to Resource Preservation in Delayed Elimination Games

A Rocq development of the following claim. An agent acts on the resources of
the world at a position in space. Other agents, the judges, may observe the act
and eliminate the agent. Signals travel at a finite speed, so a judge at
distance d sees the act after d / c and its response arrives after 2 d / c. An
agent planning over a horizon T is exposed to the judges within distance
c T / 2, a set that grows with the cube of the horizon. A destructive act is a
signal; a preserving one is not. The survival of any destructive act vanishes
as the horizon grows, at an explicit rate; an action's benefit buys it an
explicit crossover depth beyond which preservation wins; the destructiveness of
any optimal action falls like 1 / T; on any finite menu every optimal action is
eventually preserving. The judges are players too: punishing a preserver is
destruction under the same measure, so deep judges spare preservers and punish
persistent destroyers once the destruction prevented over their horizon exceeds
the cost of punishing, and in a population where every player is both agent and
judge, the strategy that preserves, spares preservers and punishes destroyers is
a Nash equilibrium at depth. The convergence survives any positive credence
that a judge is present at a site, any positive fraction of the destruction that
remains visible, and any time preference whose rate times the horizon stays
bounded; it fails for a fixed positive rate, and for judges whose decisions are
perfectly dependent. With the SI speed of light, judges at the stellar density
of the solar neighbourhood and inverse-square attenuation on the scale of their
spacing, the crossover for an act destroying one tolerance unit against an
e-fold benefit lies within 230 years of planning horizon; at the density of
bright galaxies, within 500 million years.

## Modules

`Vectors.v` defines vectors in R^3 with the Euclidean norm and proves the
metric axioms, Cauchy-Schwarz, the triangle inequality and its reverse, the
inclusion of a cube in a ball and the comparison of the l1 and Euclidean norms.
`Actions.v` defines an action as a map on the resource state and the
destruction of an event as the drop in norm it causes, clamped at zero; scaling
the state by f destroys the fraction 1 - f of it. `Sums.v` holds the finite
sums and products, sums over integer ranges, the two-sided geometric sum,
integer parts and the bounds on exp and ln used throughout.

`LightCone.v` fixes a speed of light c, a lattice spacing res and a tolerance
tol. It defines judges, reception times and the round trip, proves that the
horizon radius is c T / 2 (`within_horizon_iff`) and that no judge's reception
lies in another's causal past (`receptions_not_timelike`), builds the lattice of
potential judges within a ball, counts it from below by the inscribed cube and
from above by the enclosing one (`judges_count_lower`, `judges_count_upper`),
proves the count and the hazard monotone in the radius, bounds the hazard sum
from below by a quantity linear in the radius (`hazard_lower_bound`), and bounds
the discounted lattice sum from above by factoring it into three geometric sums
(`discount_sum_le`). Attenuation is any law bounded by one and no steeper than
inverse square; the flat, inverse-square and inverse-linear laws are instances.

`Survival.v` is the core. The elimination probability of a judge has the Poisson
form 1 - exp(- signal / tolerance), survival is the product over the judges
within the horizon, and survival = exp(- offense * hazard)
(`survival_closed_form`). The offense is any non-negative functional of the
agent's options. Beyond the depth `T_min`, survival is at most
exp(- offense * rate * T) with `rate` explicit (`survival_upper_bound`), so it
vanishes (`survival_vanishes`, `survival_Un_cv`). With a benefit function,
utility is benefit times survival; the crossover depth is explicit
(`uniform_crossover`, `pointwise_crossover`), the offense of any action at least
as good as preservation is bounded (`optimal_offense_le`,
`optimal_offense_vanishes`), the crossover is a genuine phase change
(`shallow_offense_wins`), and on a finite menu every optimal action is
eventually inoffensive (`optimal_actions_are_inoffensive`). Time preference
weights a response by exp(- r * 2 d / c); for a fixed positive rate the
discounted survival has a positive floor at every depth
(`discounted_survival_floor`) and a lucrative destructive action is preferred
at every depth (`discounting_blocks_convergence`). Weighted survival
generalises both: any per-judge weight bounded below by a positive constant on
the judges within the horizon preserves convergence with the rate multiplied by
that constant (`survival_w_upper`, `weighted_crossover`), which yields the
presence bound (`presence_survival_upper`, `presence_crossover`) and the
patience bound: time preference with r T bounded by K behaves like the
undiscounted model with rate multiplied by exp(- K)
(`patient_survival_upper`, `patient_survival_vanishes`, `patient_crossover`).
Depth is never safer for an offender (`survival_antitone_horizon`).

`Resources.v` instantiates the offense with the destruction of the event:
`preservation_survives`, `destruction_survival_rate`,
`destruction_survival_vanishes`, `destruction_survival_Un_cv`,
`preservation_crossover`, `optimal_destruction_bound`,
`optimal_destruction_vanishes`, `optimal_actions_preserve`,
`shallow_destruction_wins`, `deeper_never_safer`,
`time_preference_blocks_convergence`; a policy is judged act by act
(`preserving_policy_survives`, `destructive_policy_vanishes`); concealment that
leaves any positive fraction visible fails (`concealment_must_be_perfect`); and
the presence and patience results are restated for destruction
(`presence_destruction_decays`, `patient_destruction_vanishes`,
`presence_preservation_crossover`, `patient_preservation_crossover`).

`Judges.v` treats judges as players. A verdict is a best response to the
judge's payoffs (`judge_best_optimal`), and the Poisson elimination probability
is the agent's credence that the judge's tolerance lies below the perceived
offense (`elim_prob_is_tolerance_credence`). Punishing a preserver destroys the
preserver's resources, so the judge is a destroyer under the same measure: its
survival vanishes with its own depth (`harsh_judge_survival_vanishes`) and deep
judges spare preservers (`deep_judges_spare_preservers`). Punishing a persistent
destroyer is net-preserving once the judge's horizon exceeds the destroyer's
value over its destruction rate, and the destruction prevented over the
horizon, valued at any positive rate, exceeds any fixed cost once the horizon
exceeds cost / (w delta) (`gain_exceeds_cost`), so deep judges punish
(`deep_judges_punish_persistent_destroyers`, `derived_asymmetry`).

`Independence.v` formalises couplings of the judges' decisions. The model's
survival is the joint survival of the independent coupling
(`survival_is_independent_coupling`), any coupling has joint survival at most
one minus the largest marginal (`frechet_bound`), and the perfectly dependent
coupling attains it with a survival that does not decay with the number of
judges (`all_or_nothing_survival`).

`Population.v` defines the population game. A strategy is an act, a verdict on
preservers and a verdict on persistent destroyers; a player's benefit sums the
three decisions, punishing a preserver prevents nothing and punishing a
destroyer prevents delta * T valued at w per unit, and its one life survives
all three judgments. When every other player preserves, spares preservers and
punishes destroyers, that strategy is a best response for a deep player
whatever the signs of the benefits, and deviating to a destructive act or to
punishing preservers is strictly worse (`nice_is_nash`); any finite menu that
holds a preserving action of positive benefit holds one whose nice strategy is
such an equilibrium (`best_preserving`, `nash_exists`).

`Physical.v` instantiates the parameters. The speed of light is the SI value,
distances are measured in the judge spacing, which is also the attenuation
scale, destruction in units of tolerance, and attenuation is inverse square.
For any spacing the minimal depth is four light-crossings of the spacing and
the hazard rate per unit destruction is c / (32 spacing) per second
(`depth_min_eq`, `hazard_rate_eq`); an act destroying one tolerance unit
survives with probability at most one half, and loses to preservation against
an e-fold benefit, once the horizon exceeds the minimal depth and the
reciprocal hazard rate (`physical_half`, `physical_crossover`). At one judge
per ten cubic parsecs, the stellar density within ten parsecs of the Sun, the
minimal depth lies between 28 and 29 years, the hazard rate between 1.409e-10
and 1.41e-10 per second, and both results hold beyond 230 years
(`stellar_half_life`, `stellar_crossover`); at one judge in a million stars the
crossover lies within 450 million years (`stellar_presence_example`). At one
judge per hundred cubic megaparsecs, the density of bright galaxies, the
minimal depth lies between 60 and 62 million years and the crossover beyond
500 million years (`galactic_crossover`). The constants were checked against
WolframScript: the parsec in metres, the speed of light, the Julian year and
the cube roots that fix the spacings.

`Summary.v` states the thesis as `convergence_to_resource_preservation`, its
extensions as `beyond_the_thesis`, and the two-level game as
`two_level_equilibrium`, and prints the axioms each depends on.

## Hypotheses

The development rests on the four axioms of the standard library's
construction of the real numbers: functional extensionality, excluded middle
and the two Dedekind-reals axioms, as `coqchk` and the `Print Assumptions`
commands in `Summary.v` report. Everything else is a stated premise of a
theorem. The parameters c, res and tol are positive, which `Physical.v`
discharges by instantiation. The agent values its own survival, 0 < benefit p,
and so does a judge, 0 < b0; a preserver has positive value, 0 < phi, a
destroyer a positive rate, 0 < delta, and prevented destruction a positive
valuation, 0 < w. The model fixes the Poisson form of the elimination
probability, equivalently the exponential credence over tolerances; the
independence of the judges' decisions, justified by spacelike separation and
shown necessary in `Independence.v`; the forfeiture of the whole benefit on
elimination; time preference as a weight on each judge's verdict; the
attribution of prevented destruction to the judge's credit; additive benefits
and multiplicative survival across a player's decisions; and, in the population
game, that every other player is nice. The remaining premises are the content
of the theorems: a horizon beyond the stated depth, a time preference with r T
bounded, a presence credence q > 0, a visibility v > 0.

## Building and checking

The development uses the Rocq Prover 9.0 with its standard library and nothing
else. `make` builds the modules in dependency order and `make check` runs the
checker on the result, using `rocq compile` and `rocq check` where the `rocq`
command exists and `coqc` and `coqchk` otherwise; set `COQBIN` to the directory
of the binaries with a trailing slash if it is not on the `PATH`. On Windows,
`build.cmd` does the same with the Rocq Platform; on a Unix shell, `build.sh`
does. The continuous integration workflow builds and checks against the Rocq
9.0, 9.1 and 9.2 images.

```
make
make check
```
