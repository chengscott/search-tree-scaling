/* Guided explanations paired with the original Lean source. Math in prose uses $LaTeX$. */
window.LESSONS = [
  {
    "id": "model",
    "group": "Foundations",
    "title": "The search model",
    "subtitle": "Start with the objects the proof talks about: states, actions, scores, and observations.",
    "result": "scoreₐ = Q̂ₐ + cPₐ √m / (1 + nₐ)",
    "assumptions": [
      "MCTSModel supplies abstract values, estimates, counts, selection events, and a distinguished action isBest.",
      "Priors are nonnegative and sum to one. Regularity later makes isBest strictly better than every other action.",
      "This is a formal model of a search execution, not executable MCTS code or a browser Lean prover."
    ],
    "refs": [
      "MCTSModel",
      "puctScore",
      "Gap",
      "Suboptimal",
      "arrivalCount"
    ],
    "steps": [
      {
        "title": "Separate truth from estimates",
        "body": "Fix a state $s$ and an available action $a$. The field value represents its asymptotic value $Q(s,a)$; searchValue represents the estimate used at a particular observation time. The proof keeps these quantities separate because the selection rule acts on estimates, while suboptimality is defined using asymptotic values.\n\nThe model also records parent and action visit counts, whether a state is terminal, and which action is selected at each global time. A global time need not contain a selection at this particular state. Action depends on State, so different states may have different available actions.\n\nFinally, isBest names a distinguished action. Its name alone is not a proof of optimality: the positive value-gap assumption later establishes that every other action has smaller asymptotic value.",
        "equation": "Qₐ ≠ Q̂ₐ(t) in general",
        "ref": "MCTSModel",
        "marker": "  value :"
      },
      {
        "title": "Read the pUCT score",
        "body": "The pUCT score adds an estimated value to an exploration term. For a fixed parent count, selecting action $a$ increases its denominator and reduces its future exploration term. Increasing the parent count increases the numerator and can make an action competitive again even if it has not recently been selected.\n\nThe coefficient $c$ sets the exploration scale, and $P(s,a)$ weights that scale for the individual action. If the prior is zero, the exploration term is zero; this is why the lower visit bound for a suboptimal action explicitly requires a positive prior.\n\nGap records the difference between the asymptotic value of the optimal action and that of a. Later score comparisons show how large an exploration term is needed to compensate for this value gap. The noncomputable definition specifies this mathematical score without requiring an executable numerical implementation.",
        "equation": "Δₐ = Q* − Qₐ",
        "ref": "puctScore",
        "marker": ""
      },
      {
        "title": "Keep arrivals and selections distinct",
        "body": "The selection counters start at zero and count outgoing choices from a node. For depth analysis, Lean additionally counts the arrival that initially expands the node. This gives arrivalCount = parentVisit + 1. It does not change the numerator in the pUCT formula, which still uses the parent selection count.\n\nAlong a reached edge, the next node’s arrival count is identified with the number of selections of that edge. Since an action count is at most its parent selection count, the next arrival count is strictly smaller than the current arrival count.\n\nThis strict decrease is needed when a path enters small visit counts: a bounded positive integer count can decrease only a bounded number of times. At the root, $n$ completed sequential simulations therefore correspond to $n+1$ arrivals.",
        "equation": "V = m + 1",
        "ref": "arrivalCount",
        "marker": ""
      }
    ],
    "question": "Does isBest alone prove optimality?",
    "answer": "No. The model names an action. The positive gap condition in Regularity proves that every other action has strictly smaller true value."
  },
  {
    "id": "counts",
    "group": "Foundations",
    "title": "Count bookkeeping",
    "subtitle": "Build the discrete facts used in every asymptotic argument.",
    "result": "m(t) = Σₐ nₐ(t)",
    "assumptions": [
      "CountUpdates starts parent and child counts at zero.",
      "A selection increments its parent and selected child; idle counts stay fixed.",
      "Distinct actions cannot both be selected at the same state and time."
    ],
    "refs": [
      "MCTSModel.CountUpdates",
      "child_monotone",
      "count_identity",
      "lastSelection_spec"
    ],
    "steps": [
      {
        "title": "Counts never decrease",
        "body": "To prove that counts never decrease between arbitrary times, it is enough to compare time $t$ with $t$ + 1. If action $a$ is selected, child_selected says its count increases by exactly one. If it is not selected, child_idle says the count is unchanged. Both cases give the required inequality.\n\nFor the parent, split according to whether any action at the state is selected. The parent increments when a selection occurs and remains fixed when none occurs. Chaining these consecutive-time inequalities proves monotonicity.\n\nLater proofs compare a current count with the count at an earlier selection time. These monotonicity facts justify transferring a lower bound forward in time and an upper bound on an earlier parent count to the current parent count.",
        "equation": "nₐ(t + 1) ∈ { nₐ(t), nₐ(t) + 1 }",
        "ref": "child_monotone",
        "marker": ""
      },
      {
        "title": "The parent counts all child selections",
        "body": "Initially, every child count and the parent count are zero, so the identity holds. For the induction step, first suppose that action $a$ is selected. Selection disjointness ensures that no different action $b$ is also selected at the same state and time.\n\nConsequently, exactly one term in the sum of child counts increases by one. The parent count also increases by one, so an equality at time $t$ remains an equality at time $t$ + 1. If no action is selected, every term and the parent stay unchanged.\n\nThe private helper count_identity proves the identity directly from zero initialization. This identity is later rearranged so that parent visits minus optimal-action visits equal the sum of all suboptimal-action visits. In the successor case, ih is the count identity at the preceding time.",
        "equation": "m = Σₐ nₐ",
        "ref": "count_identity",
        "marker": ""
      },
      {
        "title": "Recover the last selection",
        "body": "Suppose the action count at observation time $t$ is positive. Because it started at zero and can increase only when the action is selected, some earlier selection must account for its final increment. The inductive proof examines whether the action is selected at the immediately preceding time; if not, it reuses the earlier witness.\n\nThe resulting time $u$ is strictly before $t$, the action was selected at $u$, and its count at $t$ equals its pre-selection count at $u$ plus one. lastSelection chooses a witness, while lastSelection_spec exposes these facts for use in later proofs.\n\nThis lets a score comparison at a selection time control a count observed later. The related eventual-constancy lemma handles the other possibility: once selections stop, the update rule forces the count to remain fixed.",
        "equation": "u < t, selectedAt(a,u), nₐ(t) = nₐ(u) + 1",
        "ref": "last_selection_exists",
        "marker": ""
      },
      {
        "title": "Selections force divergence",
        "body": "Fix a desired count $k$. The proof first shows that the action reaches at least $k$ visits at some time. For $k$ = 0 this is immediate. If the count has reached $k$, infinite selection supplies another selection at that time or later; monotonicity preserves the accumulated visits, and the selected update adds one.\n\nInduction therefore gives a time at which any chosen count threshold has been reached. Monotonicity then ensures that the count stays above that threshold at every later time. This is precisely convergence to infinity.\n\nThe distinction matters: merely having infinitely many global observation times would not imply count growth at this state. The hypothesis supplies actual selections of the action arbitrarily late.",
        "equation": "selected infinitely often ⇒ nₐ(t) → ∞",
        "ref": "child_tendsto",
        "marker": ""
      }
    ],
    "question": "Why can global time grow while a parent count stays fixed?",
    "answer": "A global time may be idle at this state. The proof uses explicit count divergence where it needs infinitely many local decisions."
  },
  {
    "id": "assumptions",
    "group": "Foundations",
    "title": "Regularity & value estimates",
    "subtitle": "Know what is supplied to Lean before interpreting a theorem’s conclusion.",
    "result": "Q̂(s,a) → Q(s,a), uniformly over states and actions in the paper",
    "assumptions": [
      "Finite branching has a common finite bound b.",
      "Every suboptimal gap lies between positive constants Δmin and Δmax.",
      "Every nonterminal state has some suboptimal action with prior at least p₀ > 0."
    ],
    "refs": [
      "Regularity",
      "ValueConsistency",
      "UniformValueConsistency",
      "MCTSModel.Sequential"
    ],
    "steps": [
      {
        "title": "Regularity controls the whole tree",
        "body": "Regularity contains three different kinds of uniform control. The branching bound limits how many suboptimal visit estimates are summed at one state. The positive lower value gap lets sufficiently accurate estimates distinguish the optimal action from every suboptimal action.\n\nThe upper value-gap bound and the positive lower prior bound serve the lower exploration estimate. At every nonterminal state there is at least one suboptimal action whose exploration term cannot become arbitrarily weak simply because its prior is tiny or its gap is huge.\n\nThe word uniform means that the same constants work across the states relevant to the theorem. This becomes essential for depth: increasing the simulation count exposes additional states, so constants chosen separately at each fixed state would not automatically control the whole growing path.",
        "equation": "0 < Δmin ≤ Δₐ ≤ Δmax",
        "ref": "Regularity",
        "marker": ""
      },
      {
        "title": "Local convergence suffices for local counts",
        "body": "ValueConsistency is a conditional convergence statement. At a state whose parent visit count tends to infinity, each action’s estimate converges to its asymptotic value. Fix an error tolerance and one action; convergence supplies a time after which that action’s error is within the tolerance.\n\nAt a fixed state there are finitely many actions. Taking a common sufficiently late time therefore makes every action estimate accurate simultaneously. The threshold may still depend on this state, which is enough for the local visit-count conclusion of Theorem 1(1).\n\nThe paper’s proof remark assumes uniform convergence over states and actions. Lean proves the local theorem with the weaker condition above, while retaining the stronger condition where a path argument needs it. In the Lean statement, $\\mathcal N(Q)$ denotes the neighborhood filter at $Q$, and an eventual statement means that its property holds for all sufficiently large observation times.",
        "equation": "mₛ(t) → ∞ ⇒ Q̂ₛ,ₐ(t) → Qₛ,ₐ",
        "ref": "ValueConsistency",
        "marker": ""
      },
      {
        "title": "Depth needs a common threshold",
        "body": "UniformValueConsistency starts with an error tolerance and supplies one parent-count threshold that works for every state, every action, and every observation. Once a state’s parent count exceeds that threshold, the estimate error is controlled regardless of which state it is.\n\nThis is stronger than choosing a convergence time separately at each state. A depth theorem studies a path that can reach new states as the simulation count grows. Without a common threshold, those newly reached states might always be outside their individual accurate-estimate ranges.\n\nThe order of the quantifiers captures this requirement: choose the tolerance, then choose the threshold, then quantify over states and actions. Uniform visit-count and one-step depth estimates inherit that independence from the state. This is expressed by the quantifier order $\\forall\\varepsilon,\\;\\exists m_0,\\;\\forall s,a,t$.",
        "equation": "m ≥ m₀(ε) ⇒ |Q̂ₛ,ₐ − Qₛ,ₐ| ≤ ε",
        "ref": "UniformValueConsistency",
        "marker": ""
      },
      {
        "title": "Selection is an explicit hypothesis",
        "body": "The count update rules describe how visits change, but do not say which action must be chosen. Sequential adds the pUCT argmax condition: whenever action $a$ is selected, its score is at least the score of every available competitor $b$.\n\nThe proof can instantiate $b$ with the optimal action when a suboptimal action is selected, giving an upper bound on that action’s count. At a selection of the optimal action, it instantiates $b$ with a suboptimal competitor, giving the comparison used for the lower bound.\n\nThese implications apply at actual selection times. They do not require a selection at every global time. That is why the proofs explicitly locate a suitable selection time before invoking argmax.",
        "equation": "selected(a,t) ⇒ scoreᵦ(t) ≤ scoreₐ(t)",
        "ref": "MCTSModel.Sequential",
        "marker": ""
      }
    ],
    "question": "Does the formalization prove value estimates converge?",
    "answer": "The execution results discussed here assume convergence of value estimates. The paper states uniform convergence; Lean uses ValueConsistency locally and UniformValueConsistency for depth bounds. They derive visit and depth consequences under that hypothesis."
  },
  {
    "id": "caps",
    "group": "Foundations",
    "title": "Finite terminal depth",
    "subtitle": "The depth estimates hold until capped by a fixed terminal depth $L$. This chapter introduces that convention; the later steps explain the capped results for each setting.",
    "result": "Hₒₚₜ(n) = L eventually",
    "assumptions": [
      "Capped path predicates impose H ≤ L. The condition that the optimal child at the deepest reached node has zero visits is required only while H < L.",
      "Theorem 1(2), Theorem 2, Theorem 3, and Theorem 4 each have capped counterparts.",
      "The capped corollaries derive their rates from the search execution and capped path identities."
    ],
    "refs": [
      "theorem1_part2_capped",
      "theorem2_capped",
      "theorem3_capped",
      "theorem4_capped",
      "corollary21_capped",
      "corollary22_capped",
      "corollary23_capped"
    ],
    "steps": [
      {
        "title": "Distinguish reaching the terminal depth",
        "body": "A capped path has reached depth $H$ at most $L$. If $H$ is strictly below $L$, it must still end at a nonterminal node whose optimal child has zero visits. If $H$ equals $L$, the path has already reached the cap and no such unvisited-child requirement is imposed there.\n\nThis distinction avoids treating a reached terminal depth as a failure to extend an otherwise uncapped path. It also handles $L=0$: the inequality $H\\le0$ immediately forces depth zero, so no progress or nonterminal-root premise is needed.\n\nThe Lean predicate describes a path capped at any fixed depth; it does not itself assert that the state at $L$ is terminal. The paper applies this formulation with $L$ equal to the terminal depth of the optimal path.",
        "equation": "H ≤ L; H < L ⇒ the optimal child at depth H has zero visits",
        "ref": "CappedOptimalPathCounts",
        "marker": ""
      },
      {
        "title": "Constant c: the terminal node is eventually reached",
        "body": "Suppose the path were still below the fixed cap $L$ at an arbitrarily large simulation count. Its deepest reached node would have an unvisited optimal child, so the uniform upper difference estimate would bound its arrival count and hence its square root.\n\nAlong every reached edge, the same upper difference bound controls the decrease in the square-root quantity. Summing across at most $L$ edges therefore bounds the root square root by a fixed endpoint term plus a constant times $L$.\n\nThe root arrival count is $n+1$, whose square root tends to infinity. This contradicts the fixed bound once $n$ is large enough. The path must then have $H=L$. This is eventual equality, stronger than merely saying that the depth stays within a constant factor of $L$.",
        "equation": "√(n + 1) ≤ bounded endpoint term + C L",
        "ref": "theorem1_part2_capped",
        "marker": ""
      },
      {
        "title": "General c(·): the terminal node is eventually reached",
        "body": "The capped scheduled theorem accepts either of two sufficient conditions. If the exploration scale $c(n)\\sqrt n$ is little-o of $n$, the total suboptimal count upper bound is sublinear, leaving a positive fraction of visits for the optimal action at large counts.\n\nAlternatively, uniformly positive optimal priors give an optimal-share estimate directly, even when exploration is not sublinear. In either case, a uniformly positive fraction of a large parent count continues into its optimal child.\n\nFor a fixed number $L$ of levels, applying that share estimate repeatedly preserves divergence of the counts along the path as the root count grows. An unvisited optimal child at any earlier level would contradict the resulting large-count bound. Thus the optimal path eventually reaches the cap.",
        "equation": "F(n) = o(n) OR positive optimal priors ⇒ H = L eventually",
        "ref": "theorem2_capped",
        "marker": ""
      },
      {
        "title": "Parallel caps need no contention",
        "body": "The parallel capped result uses only upper estimates on the count difference, together with the $O(T)$ bound at an unvisited optimal child. Along a reached path of depth at most $L$, every arrival count is at most the root count, so each square-root contribution is at most of order $\\sqrt n$.\n\nIf the cap were not reached, summing the upper differences across at most $L$ edges and adding the endpoint bound would make the root count at most a constant multiple of $L\\sqrt n+LT+T$. With $L$ fixed and $T=o(n)$, every term on this upper bound is sublinear in $n$.\n\nThat cannot account for a root arrival count of $n+1$ once $n$ is large. Hence the cap is eventually reached. No lower count-difference estimate is needed in this contradiction, which is why the contention hypothesis can be omitted.",
        "equation": "T = o(n) ⇒ H(n,T(n)) = L eventually",
        "ref": "theorem4_capped",
        "marker": ""
      },
      {
        "title": "Interpret the capped corollaries precisely",
        "body": "The capped corollaries compare depth with $\\min\\{D,\\operatorname{rate}(n)\\}$ for a fixed finite depth $D$. Corollaries 2.1 and 2.2 first prove that the optimal path eventually reaches $D$, then return both that equality and the appropriate capped rates.\n\nThe private helper finite_depth_capped_rate only needs depth bounded by $D$, eventual positive depth when $D>0$, and a positive lower bound on the comparison function. The public corollaries now derive these premises from the search model; they are not supplied as independent depth assumptions.\n\nCorollary 2.3 also proves eventual arrival internally, but its public conclusion returns only the three capped rates. The case $D=0$ is included: both the depth and the capped comparison are zero.",
        "equation": "H = Θ(min(D, rate(n)))",
        "ref": "finite_depth_capped_rate",
        "marker": ""
      }
    ],
    "question": "What changes when L = 0?",
    "answer": "The capped path condition already forces H = 0. The bounded-depth comparison treats this case separately, so it does not require a positive depth."
  },
  {
    "id": "lemma1",
    "group": "Preparatory lemmas",
    "title": "Lemma 1 · Selected infinitely often",
    "subtitle": "For a state $s$, every child with $P(s,a)$ > 0 is selected infinitely often as $N(s)$ → ∞.",
    "result": "Pₐ > 0 ⇒ a is selected infinitely often",
    "assumptions": [
      "Positive fixed c; sequential pUCT; regularity; value consistency.",
      "The parent count tends to infinity and the action has positive prior."
    ],
    "refs": [
      "lemma1",
      "child_eventually_constant",
      "child_tendsto"
    ],
    "steps": [
      {
        "title": "Establish future selections and normalize the score",
        "body": "The declaration states the hypotheses explicitly: a positive exploration coefficient, sequential execution, regularity, and convergence of the value estimates. Fix an infinitely visited state and an action with positive prior. Regularity supplies the finite action space used later in the proof.\n\nThe local-selection helper shows that a selection must occur after any chosen time. Otherwise the parent count would remain constant, contradicting its divergence.\n\nThe score-limit helper divides the pUCT score by the square root of the parent count. The convergent value estimate divided by this diverging square root tends to zero. Thus any limit of the normalized exploration contribution is also the limit of the normalized score. The next step applies this helper to an action assumed to be selected only finitely often.",
        "equation": "scoreₐ / √m → A = cPₐ / (1 + k) > 0",
        "ref": "lemma1",
        "marker": ""
      },
      {
        "title": "A neglected action keeps a positive normalized bonus",
        "body": "Suppose that action $a$ is selected only finitely many times. Then, after some point, $N(s,a)=n_0$ becomes a constant while $m:=N(s)$ tends to infinity. By convergence of the value estimates, $\\widehat Q(s,a)=O(1)$.\n\nDivide its pUCT score by $\\sqrt m$. The estimated-value contribution tends to zero, while the exploration contribution tends to $cP(s,a)/(1+n_0)>0$. Thus the normalized score of this child converges to a positive constant.\n\nThe paper lets $S$ be the set of children selected only finitely often. The assumed child belongs to $S$. The next step compares such children with children outside $S$, whose visit counts tend to infinity. The formal statement makes the positive coefficient $c>0$, sequential pUCT execution, regularity, and value consistency explicit.",
        "equation": "scoreₐ / √m → A = cPₐ / (1 + k) > 0",
        "ref": "lemma1",
        "marker": "  by_contra ha"
      },
      {
        "title": "Every possible competitor loses eventually",
        "body": "For every child $b\\notin S$, the visit count $N(s,b)$ tends to infinity. Its normalized exploration term $cP(s,b)/(1+N(s,b))$ therefore tends to zero. Its estimated-value term divided by $\\sqrt m$ also tends to zero, since the value estimate converges.\n\nFor the chosen positive-prior child $a\\in S$, the normalized score instead has a positive limit. Consequently, for all sufficiently large parent visit counts, a child outside $S$ cannot have a score as large as that of $a$.\n\nA child inside $S$ is eventually never selected by definition. Lean expresses these two cases separately: an infinitely selected competitor eventually has a smaller normalized score, and a finitely selected competitor eventually cannot be the selected child.",
        "equation": "selected(b,t) ⇒ scoreᵦ / √m < scoreₐ / √m",
        "ref": "lemma1",
        "marker": "  have hcomparison"
      },
      {
        "title": "Finiteness makes the contradiction simultaneous",
        "body": "Since there are finitely many children, choose a common time after which all of the preceding comparisons hold and no child in $S$ is selected again. Such a common time is obtained by combining finitely many eventual statements.\n\nThe parent visit count tends to infinity, so another selection must occur at the state after that time. Otherwise the parent count would remain constant. The selected child cannot lie outside $S$, because its score would be smaller than the score of $a$. It cannot lie inside $S$, because every child there has already had its last selection.\n\nThis contradicts the pUCT selection rule. Thus every child with $P(s,a)>0$ is selected infinitely often as $N(s)\\to\\infty$. Filter.eventually_all combines the finitely many eventual comparisons; the final inequality contradicts argmax.",
        "equation": "argmax + strict competitor advantage ⇒ contradiction",
        "ref": "lemma1",
        "marker": "  have hall"
      }
    ],
    "question": "Why divide the score by √m?",
    "answer": "It removes the growing exploration factor. A neglected positive-prior action then has a positive limit, while an infinitely selected action has limit zero."
  },
  {
    "id": "lemma2",
    "group": "Preparatory lemmas",
    "title": "Lemma 2 · Non-selected infinitely often",
    "subtitle": "For a state $s$, every child with $P(s,a)$ < 1 is non-selected infinitely often as $N(s)$ → ∞.",
    "result": "Pₐ < 1 ⇒ infinitely many local selections avoid a",
    "assumptions": [
      "The same sequential and convergence hypotheses as Lemma 1.",
      "The parent is infinitely visited; Pₐ < 1."
    ],
    "refs": [
      "lemma2",
      "NonSelectedInfinitelyOften",
      "lemma1"
    ],
    "steps": [
      {
        "title": "Find a positive-prior competitor",
        "body": "Since $P(s,a)<1$ and the priors sum to one, there exists a child $b\\ne a$ with $P(s,b)>0$. To see this, suppose every other child had zero prior. Then the sum of all priors would equal $P(s,a)$, contradicting its strict inequality with one.\n\nNonnegativity is used here: the prior mass outside $a$ cannot be positive without at least one positive term. No particular lower bound on $P(s,b)$ is needed, only strict positivity.\n\nThis is exactly the condition required to apply Lemma 1 to $b$. The rest of the proof transfers its infinitely many selections into infinitely many times at which $a$ is not selected. The source uses tsum_eq_single to reduce the prior sum under this supposition. The execution and convergence hypotheses are the same as those used in Lemma 1.",
        "equation": "Σᵦ Pᵦ = 1, Pₐ < 1 ⇒ ∃ b ≠ a, Pᵦ > 0",
        "ref": "lemma2",
        "marker": "  have hcompeting"
      },
      {
        "title": "Invoke Lemma 1 and disjointness",
        "body": "By Lemma 1, $b$ is selected infinitely often as $N(s)\\to\\infty$. Fix any starting time and choose a later time at which $b$ is selected. Since $b\\ne a$, the selection-disjointness condition implies that $a$ is not selected at that time.\n\nThe same argument works after every starting time. Hence $a$ is non-selected infinitely often, as claimed in the paper.\n\nLean makes the meaning of non-selection explicit: there must be an actual selection at the state, and that selection must choose another action. Merely observing infinitely many global times at which this state is idle would not prove the result. The witness supplied by the selection of $b$ satisfies both requirements.",
        "equation": "selected(b,t) ∧ b ≠ a ⇒ ¬selected(a,t)",
        "ref": "lemma2",
        "marker": "  obtain ⟨b, hba, hb⟩"
      }
    ],
    "question": "Would infinitely many idle times prove this lemma?",
    "answer": "No. NonSelectedInfinitelyOften explicitly requires an actual selection of another action at the state."
  },
  {
    "id": "lemma3",
    "group": "Preparatory lemmas",
    "title": "Lemma 3 · Exploration term is o(1)",
    "subtitle": "For a state $s$, let $m$ = $N(s)$ and $n_*$ = $N$($s$,a*). If $m$ − $n_*$ = $O(\\sqrt m)$, the optimal-action exploration term is o(1).",
    "result": "m − n* = O(√m) ⇒ cP*√m / (1 + n*) → 0",
    "assumptions": [
      "m tends to infinity; c > 0 and P ≥ 0.",
      "The deficit m − n* is O(√m). This is the input to the lemma."
    ],
    "refs": [
      "lemma3",
      "lemma3_bonus_bound_from_count_gap"
    ],
    "steps": [
      {
        "title": "Turn the deficit into a large denominator",
        "body": "Let $m=N(s)$ and $n_*=N(s,a^*)$. Since $m-n_*=O(\\sqrt m)$, there exists a constant $C$ such that $m-n_*\\le C\\sqrt m$ for all sufficiently large $m$. Rearranging gives $m-C\\sqrt m\\le n_*$.\n\nFor sufficiently large $m$, we also have $C\\sqrt m\\le m/2$. Therefore $n_*\\ge m/2$, so the denominator $1+n_*$ is positive and has a linear lower bound in $m$.\n\nThis is the estimate needed to compare the optimal-action exploration term with a negative power of $m$. The numerator grows as $\\sqrt m$, whereas the denominator grows at least as fast as a positive multiple of $m$. Positivity of the denominators justifies the cross multiplication in div_le_div_iff₀. Lean allows the parent count to vary with observation time as $m(t)$; the argument applies along times for which this count tends to infinity.",
        "equation": "n* ≥ m / 2 eventually",
        "ref": "lemma3_bonus_bound_from_count_gap",
        "marker": ""
      },
      {
        "title": "Squeeze the bonus to zero",
        "body": "Using the lower bound on $n_*$, the paper obtains $\\sqrt m/(1+n_*)=O(m^{-1/2})=o(1)$. Multiplication by the fixed nonnegative factor $cP(s,a^*)$ preserves convergence to zero.\n\nLean proves this through an explicit bound: $0\\le cP\\sqrt m/(1+n_*)\\le 2cP/\\sqrt m$ for all sufficiently large $m$. Since the right-hand side tends to zero, the squeeze theorem gives the conclusion.\n\nThe code then expresses convergence to zero as little-o of the constant function one, which is the paper’s $o(1)$. Strict positivity of the optimal prior is unnecessary: when that prior is zero, the exploration term is already identically zero.",
        "equation": "0 ≤ cP√m / (1 + n*) ≤ 2cP / √m → 0",
        "ref": "lemma3",
        "marker": "  have hlim"
      }
    ],
    "question": "Is a positive optimal prior needed?",
    "answer": "No. The lemma assumes only P ≥ 0. When P = 0 the bonus is identically zero."
  },
  {
    "id": "theorem1-1",
    "group": "Constant exploration coefficient",
    "title": "Theorem 1(1) · Suboptimal visit counts",
    "subtitle": "For each state $s$ with $N(s)$ → ∞ and every suboptimal action $a$ ≠ a*($s$) with $P(s,a)$ > 0, the visit count satisfies $N(s,a)$ = Θ(√$N(s)$).",
    "result": "N(s,a) = Θ(√N(s))",
    "assumptions": [
      "c > 0; Sequential c; Regularity; ValueConsistency.",
      "The fixed parent is infinitely visited.",
      "a is suboptimal and Pₐ > 0. No positive optimal-prior assumption is needed."
    ],
    "refs": [
      "theorem1_part1",
      "suboptimal_visit_upper_bound",
      "theorem1_part1_lower_case",
      "last_optimal_parent_ge_half",
      "lemma3"
    ],
    "steps": [
      {
        "title": "State the two-sided goal",
        "body": "We prove this result by first showing the upper bound and then proving the lower bound. Fix a state $s$ with $N(s)\\to\\infty$ and a suboptimal action $a_i$ with $P(s,a_i)>0$.\n\nFollowing the paper, write $m=N(s)$, $n_i=N(s,a_i)$, $P_i=P(s,a_i)$, and $\\Delta_i=Q_*-Q_i$. We need to prove both $n_i=O(\\sqrt m)$ and $n_i=\\Omega(\\sqrt m)$. The implicit constants may depend on the fixed action but must be independent of $m$.\n\nThe upper bound also controls the sum of visits to suboptimal actions. This yields the estimate $m-n_*=O(\\sqrt m)$ required by Lemma 3, which is then used in the lower-bound argument. The paper’s proof remark assumes uniform convergence over states and actions. Lean proves this local result using the weaker ValueConsistency condition at the fixed infinitely visited state.",
        "equation": "k√m ≤ nₐ ≤ K′√m eventually",
        "ref": "theorem1_part1",
        "marker": ""
      },
      {
        "title": "Consider the last optimal selection",
        "body": "For the lower bound, the paper fixes a large $m$ and considers the last visit count $\\widetilde m\\le m$ at which $a^*$ is selected. The comparison must be made at an actual optimal selection, because only then does pUCT guarantee that its score is at least that of $a_i$.\n\nLean records the corresponding global selection time as $u(t)$. Its preliminary helper proves that the last selection time tends to infinity whenever the action is selected infinitely often. Otherwise the current action count would remain bounded by the count at a fixed earlier time plus one.\n\nThis allows convergence of the value estimates to be used at those comparison times. Infinite selection of the optimal action is established later from the upper visit bound; it is not assumed at this point.",
        "equation": "optimal selected infinitely often ⇒ u(t) → ∞",
        "ref": "theorem1_part1",
        "marker": "  have hlocal_last_tendsto"
      },
      {
        "title": "Stabilize all values at this state",
        "body": "By convergence of the value estimates, choose an error tolerance smaller than a fixed fraction of $\\Delta_{\\min}$. For all sufficiently large visit counts, the estimates of the suboptimal and optimal actions differ from $Q_i$ and $Q_*$ by at most this tolerance.\n\nAt the fixed state there are finitely many actions, so one sufficiently late time works for all of them. Lean uses tolerance $\\Delta/4$, where $\\Delta$ is its positive lower bound on the value gaps, and calls the common time $t_0$.\n\nTo state the subsequent count bound, it sets $m_\\varepsilon=m(t_0)+1$. Parent-count monotonicity ensures that reaching this count requires a time at least $t_0$. Thus the estimates are uniformly accurate over the actions whenever the parent count exceeds this threshold.",
        "equation": "|Q̂ᵦ − Qᵦ| ≤ Δ / 4 for every b",
        "ref": "theorem1_part1",
        "marker": "  have hvalues_eventually"
      },
      {
        "title": "Bound every suboptimal count above",
        "body": "If a suboptimal child $a_i$ is selected when the parent has $m$ visits, its pUCT score is at least the estimated value of the optimal child: $\\widehat Q_i+cP_i\\sqrt m/(1+n_i)\\ge\\widehat Q_*$. The optimal exploration term is nonnegative, so omitting it preserves this inequality.\n\nSince $\\widehat Q_i\\le Q_i+\\varepsilon$ and $\\widehat Q_*\\ge Q_*-\\varepsilon$, rearranging yields $cP_i\\sqrt m/(1+n_i)\\ge\\Delta_i-2\\varepsilon$. Solving for $n_i$ gives an upper bound proportional to $\\sqrt m$, hence $n_i=O(\\sqrt m)$ at selection times.\n\nLean applies this at the action’s last selection, includes the increment caused by that selection, and uses parent-count monotonicity to transfer the estimate to the current time. Earlier selections are covered by a fixed constant. With $P_i\\le1$, it obtains $n_i(t)\\le K+A\\sqrt{m(t)}$. The helpers theorem1_part1_upper_case and suboptimal_visit_upper_bound carry out the score comparison and the transfer from the last selection.",
        "equation": "nᵦ(t) ≤ K + A√m(t), for b ≠ *",
        "ref": "theorem1_part1",
        "marker": "  let K :"
      },
      {
        "title": "Sum over suboptimal actions",
        "body": "Summing the upper bound over suboptimal actions yields $\\sum_{i\\ne *}n_i\\le C\\sqrt m$ for all sufficiently large $m$. The bounded branching factor ensures that the finite sum has a constant independent of the current count.\n\nThe count identity now gives $n_*=m-\\sum_{i\\ne *}n_i\\ge m-C\\sqrt m$. Equivalently, $m-n_*=O(\\sqrt m)$, which verifies the assumption in Lemma 3.\n\nIn Lean, each summand first has an upper bound $K+A\\sqrt m$. Once $\\sqrt m\\ge1$, the additive constant can be absorbed into the square-root term. The code chooses $C=b(K+A)+1$ as a convenient positive uniform constant over the actions at this state.",
        "equation": "m − n* ≤ C√m eventually",
        "ref": "theorem1_part1",
        "marker": "  have hgap :"
      },
      {
        "title": "Recover optimal selection and vanishing bonus",
        "body": "The estimate $n_*\\ge m-C\\sqrt m$ implies that the optimal action receives a number of visits tending to infinity. If it were selected only finitely often, its count would eventually be a fixed constant, contradicting this lower bound as $m\\to\\infty$.\n\nConsequently, the last optimal selection times also tend to infinity. The convergence bounds for $\\widehat Q_i$ and $\\widehat Q_*$ therefore apply at those times. By Lemma 3, the optimal exploration term is $o(1)$ there as well.\n\nThus, for all sufficiently large counts, the optimal exploration term can be made at most $\\varepsilon$, and both estimate errors can be made at most $\\varepsilon$. These are precisely the three error contributions used in the following score comparison. In the source, hvalue transfers convergence along hu, and hbonus applies lemma3 to the visit-deficit bound.",
        "equation": "n* ≥ m − C√m;  bonus* → 0",
        "ref": "theorem1_part1",
        "marker": "  have hselected"
      },
      {
        "title": "Complete the upper bound",
        "body": "The upper-bound argument has already shown $n_i\\le K+A\\sqrt m$. For $\\sqrt m\\ge1$, this implies $n_i\\le(K+A)\\sqrt m$, giving one half of the desired $\\Theta$ statement.\n\nFor the lower half, Lean chooses a positive constant $\\beta=cP_i/(\\Delta_i+3)$. This corresponds to using the fixed tolerance $\\varepsilon=1$ at sufficiently late optimal selections. Such a tolerance is enough because only a positive constant multiple of $\\sqrt m$ is required.\n\nThe helper theta_of_eventual_sandwich combines the two eventual inequalities. Its upper branch is now complete; its lower branch will use $\\beta/4$ after transferring the comparison from the last optimal selection to the current count.",
        "equation": "nₐ ≤ (K + A)√m",
        "ref": "theorem1_part1",
        "marker": "  have hΔ :"
      },
      {
        "title": "Compare scores at the last optimal selection",
        "body": "At the visit $\\widetilde m$, since $a^*$ is selected, its score is at least that of $a_i$. Thus $\\widehat Q_i+cP_i\\sqrt{\\widetilde m}/(1+n_i)\\le\\widehat Q_*+cP_*\\sqrt{\\widetilde m}/(1+n_*)$.\n\nBy Lemma 3, the optimal exploration term is at most $\\varepsilon$ for sufficiently large $m$. Also, $\\widehat Q_i\\ge Q_i-\\varepsilon$ and $\\widehat Q_*\\le Q_*+\\varepsilon$. Rearranging therefore gives $cP_i\\sqrt{\\widetilde m}/(1+n_i)\\le\\Delta_i+3\\varepsilon$.\n\nSolving for $n_i$ yields $n_i(\\widetilde m)\\ge\\beta\\sqrt{\\widetilde m}-1$ for some $\\beta>0$. Lean’s theorem1_part1_lower_case carries out this algebra, with the value of $\\beta$ chosen in the preceding step.",
        "equation": "nₐ(u) ≥ β√m(u) − 1",
        "ref": "theorem1_part1",
        "marker": "    have hlow :="
      },
      {
        "title": "Transfer the bound to the current time",
        "body": "The upper visit estimate implies that the last optimal selection occurs at a parent count $\\widetilde m\\ge m/2$ for all sufficiently large $m$. In Lean, the count identity at the last selection includes its final increment; the resulting fixed one is absorbed when deriving the same half-count bound.\n\nSince $n_i$ is nondecreasing, $n_i(m)\\ge n_i(\\widetilde m)\\ge\\beta\\sqrt{\\widetilde m}-1$. The paper uses $\\sqrt{\\widetilde m}\\ge\\sqrt m/\\sqrt2$. Lean uses the slightly weaker bound $\\sqrt{\\widetilde m}\\ge\\sqrt m/2$, which suffices for the asymptotic order.\n\nFor sufficiently large $m$, the subtractive one is absorbed into another fixed factor, giving $n_i(m)\\ge(\\beta/4)\\sqrt m$. Hence $n_i=\\Omega(\\sqrt m)$. Together with the upper bound, this establishes $N(s,a_i)=\\Theta(\\sqrt{N(s)})$. The fact hmono transfers the lower count bound forward from the last selection time.",
        "equation": "(β/4)√m(t) ≤ nₐ(t) ≤ (K + A)√m(t)",
        "ref": "theorem1_part1",
        "marker": "    have hroot :"
      }
    ],
    "question": "Why not use a score comparison at the current time?",
    "answer": "The optimal action may not be selected now. Argmax only supplies the needed comparison at a selection of the optimal action. The last-selection argument bridges that time to the current count."
  },
  {
    "id": "depth-tools",
    "group": "Constant exploration coefficient",
    "title": "From visits to depth",
    "subtitle": "$A$ change of potential turns variable count losses into roughly constant progress per edge.",
    "result": "Vₓ − Vₓ₊₁ = Θ(√Vₓ)",
    "assumptions": [
      "Uniform convergence of the value estimates gives a threshold independent of the state.",
      "Reached edges identify child visits with the next node’s arrival count.",
      "Before the terminal cap is reached, the optimal child at the deepest reached node has zero visits."
    ],
    "refs": [
      "uniform_arrival_optimal_difference",
      "finite_chain_cutoff",
      "unvisited_arrival_bound",
      "CountPath"
    ],
    "steps": [
      {
        "title": "Use arrivals along a reached path",
        "body": "Consider two consecutive reached nodes on the optimal path. The count assigned to the child is the number of selections of the edge leading to it. That count cannot exceed the parent’s total number of outgoing selections.\n\nLean’s path quantity $V$ additionally includes the parent’s initial expansion arrival. Therefore the child’s count is at most $V$ minus one, giving strict decrease along every reached edge. This holds independently of the asymptotic visit estimates.\n\nThe integer-valued decrease is particularly useful near the bottom of the path. Once $V$ is below a fixed threshold, only a bounded number of additional positive levels can remain. It allows the proof to concentrate its analytical estimates on the prefix where counts are large. CountPath packages these positivity and strict-decrease conditions together with the root count.",
        "equation": "Vₓ₊₁ ≤ Vₓ − 1",
        "ref": "CountPath",
        "marker": ""
      },
      {
        "title": "Make the optimal-edge loss uniform",
        "body": "At a nonterminal node, the difference between the parent selection count and the optimal-action count is the sum of the suboptimal-action counts. Uniform versions of the upper visit bounds therefore give an upper bound proportional to the square root of the parent count.\n\nFor the lower bound, regularity supplies at least one suboptimal action with prior bounded below by $p_0$ and value gap bounded above by $\\Delta_{\\max}$. Its lower visit estimate forces a square-root number of visits away from the optimal action. Uniform convergence makes the constants and thresholds independent of the particular node.\n\nConverting selection counts to arrival counts changes the difference by a fixed one and changes a square root only by comparable factors at large counts. Thus one pair of positive constants controls every sufficiently large optimal-path edge. These estimates are derived uniformly from the score comparisons; separate pointwise Theta statements would not by themselves supply the required common constants.",
        "equation": "κ√Vₓ ≤ Vₓ − Vₓ₊₁ ≤ C√Vₓ",
        "ref": "uniform_arrival_optimal_difference",
        "marker": ""
      },
      {
        "title": "Cut off the small-count tail",
        "body": "The one-step estimates are available only above a fixed visit threshold. Split the path at the first node below that threshold. The earlier nodes form the prefix where the analytical bounds apply; the remaining strictly decreasing integer counts give a bounded tail.\n\nWe must also rule out a path ending while its last count is still arbitrarily large. Before a terminal cap is reached, the optimal child of the deepest reached node has zero visits. At that node the upper difference bound reduces to $V\\le C\\sqrt V$, which forces $V\\le C^2$.\n\nChoose the cutoff above this endpoint bound. The prefix then ends with bounded count whether it stops at the cutoff or at the deepest reached node. In the paper’s notation the full optimal depth differs from the cutoff depth by $O(1)$; Lean keeps separate variables for these two depths.",
        "equation": "Vₕ ≤ C²",
        "ref": "unvisited_arrival_bound",
        "marker": ""
      },
      {
        "title": "Choose the square-root potential",
        "body": "The raw difference $V_x-V_{x+1}$ varies with the current count, so summing it directly does not immediately count the number of edges. Instead compare the square roots of consecutive counts using the difference-of-squares identity shown below.\n\nThe denominator lies between $\\sqrt{V_x}$ and twice $\\sqrt{V_x}$ because the child count is nonnegative and no larger than the parent count. Dividing the two-sided visit difference estimate therefore bounds each square-root difference between $\\frac\\kappa2$ and $C$.\n\nNow every large-count edge contributes between two fixed positive amounts. Summing these differences cancels all intermediate square roots, leaving only the root and the cutoff endpoint. This converts control of visit counts into control of path length.",
        "equation": "√Vₓ − √Vₓ₊₁ = (Vₓ − Vₓ₊₁)/(√Vₓ + √Vₓ₊₁)",
        "ref": "theorem1_part2",
        "marker": "    have hsteps"
      }
    ],
    "question": "Why add the expansion arrival?",
    "answer": "Selection counts alone need not strictly decrease along a reached edge. Arrival count = parent selections + 1 supplies strict decrease and controls the finite tail."
  },
  {
    "id": "theorem1-2",
    "group": "Constant exploration coefficient",
    "title": "Theorem 1(2) · Depth of the optimal path",
    "subtitle": "The maximum depth reached along the optimal path satisfies $H_{\\mathrm{opt}}$ = $\\Theta(\\sqrt n)$, until capped by a finite terminal depth.",
    "result": "Hₒₚₜ(n) = Θ(√n)",
    "assumptions": [
      "Positive fixed c; Sequential; Regularity; UniformValueConsistency.",
      "For the uncapped Lean statement, the deepest reached node on the optimal path is eventually nonterminal and its optimal child has zero visits.",
      "The root arrival count is n + 1 after n completed simulations."
    ],
    "refs": [
      "theorem1_part2",
      "uniform_arrival_optimal_difference",
      "sqrtSimulationCount_succ_equiv"
    ],
    "steps": [
      {
        "title": "Collect uniform visit-count bounds",
        "body": "Let $s_x$ be the node on the optimal path at depth $x$, and let $N_x:=N(s_x)$. Following the paper, take $H$ to be the first depth below a sufficiently large fixed visit count. The remaining tail has $O(1)$ edges, so $H_{\\mathrm{opt}}=H+O(1)$.\n\nFor the upper depth bound, regularity supplies a suboptimal action whose prior is uniformly bounded below. Applying the lower visit bound to this action gives $N_x-N_{x+1}\\ge c\\sqrt{N_x}$ above a fixed threshold, after absorbing the additive constant.\n\nFor the lower depth bound, summing the upper visit bounds gives $N_x-N_{x+1}\\le C\\sqrt{N_x}$. Lean states these comparisons with arrival counts $V_x$ and chooses its cutoff above the bound for the deepest reached node. The constants work uniformly along the large-count prefix.",
        "equation": "κ√V ≤ V − Vnext ≤ C√V",
        "ref": "theorem1_part2",
        "marker": "  obtain ⟨κ"
      },
      {
        "title": "Upper bound by Riemann comparison",
        "body": "We first prove the asymptotic upper bound on depth. Since $y\\mapsto1/\\sqrt y$ is decreasing, the rectangle of width $N_x-N_{x+1}$ and height $1/\\sqrt{N_x}$ lies below the integral over $[N_{x+1},N_x]$.\n\nTherefore $(N_x-N_{x+1})/\\sqrt{N_x}\\le\\int_{N_{x+1}}^{N_x}\\mathrm{d}y/\\sqrt y$. The lower one-step estimate bounds the left side below by a positive constant. Summing along the optimal path makes the adjacent integrals combine into $\\int_{N_H}^n\\mathrm{d}y/\\sqrt y\\le2\\sqrt n$.\n\nThus $H=O(\\sqrt n)$, and adding the bounded remaining tail gives $H_{\\mathrm{opt}}=O(\\sqrt n)$. Lean obtains the equivalent estimate by bounding and summing the square-root differences, using the antiderivative of the same integrand. The corresponding inequality in Lean is $H(n)\\le(2/\\kappa)\\sqrt{n+1}+m$, where $m$ is a fixed cutoff.",
        "equation": "√(n + 1) − √m ≤ C H(n)",
        "ref": "theorem1_part2",
        "marker": "  have hbounds"
      },
      {
        "title": "Lower bound and conclusion",
        "body": "For the reverse inequality, $N_x-N_{x+1}=O(\\sqrt{N_x})$ allows the fixed threshold to be chosen so that $N_{x+1}\\ge N_x/2>0$. The integral over one edge is then at most $(N_x-N_{x+1})/\\sqrt{N_{x+1}}$, which is bounded by a constant because $\\sqrt{N_x/N_{x+1}}\\le\\sqrt2$.\n\nSumming along the path gives $\\int_{N_H}^n\\mathrm{d}y/\\sqrt y\\le C'H$. Since the endpoint count is bounded, the integral is of order $\\sqrt n$, and hence $H_{\\mathrm{opt}}=\\Omega(\\sqrt n)$. Together, the bounds establish $H_{\\mathrm{opt}}=\\Theta(\\sqrt n)$.\n\nLean performs the equivalent telescoping calculation with root arrival count $n+1$, absorbs the fixed cutoff terms, and uses $\\sqrt{n+1}=\\Theta(\\sqrt n)$. The finite terminal depth is handled separately by the capped theorem.",
        "equation": "H(n) = Θ(√(n + 1)) = Θ(√n)",
        "ref": "sqrtSimulationCount_succ_equiv",
        "marker": ""
      }
    ],
    "question": "Does this say a finite tree has unbounded depth?",
    "answer": "No. This Lean statement assumes the reached optimal path still ends at a nonterminal node whose optimal child has zero visits. The capped statement proves that Hₒₚₜ eventually equals the fixed terminal depth L."
  },
  {
    "id": "theorem1-3",
    "group": "Constant exploration coefficient",
    "title": "Theorem 1(3) · Maximum tree depth",
    "subtitle": "The maximum depth of the search tree satisfies $H_{\\max}$ = $O(\\sqrt n)$. Lean proves the upper bound for every reached path, including a longest path.",
    "result": "Hₘₐₓ(n) = O(√n)",
    "assumptions": [
      "The same uniform sequential assumptions as Theorem 1(2).",
      "A reached path may choose arbitrary actions; its root arrival count is n + 1."
    ],
    "refs": [
      "theorem1_part3",
      "uniform_arrival_optimal_difference",
      "suboptimal_visit_upper_of_value_estimates"
    ],
    "steps": [
      {
        "title": "Bound the loss on any edge",
        "body": "Fix any reached edge, allowing its chosen action to be either optimal or suboptimal. If it is optimal, the uniform lower visit-difference estimate already gives a loss of at least a positive multiple of the square root of the parent arrival count.\n\nIf the action is suboptimal, its child count has a uniform upper bound $K+A\\sqrt m$. Subtracting this from a parent count of order $m$ leaves a much larger difference. Above a sufficiently large common threshold, that difference is also at least a positive multiple of $\\sqrt V$.\n\nChoose one smaller positive constant and one larger threshold that work in both cases. This produces a lower difference estimate along every reached path. Unlike Theorem 1(2), no assumption that each edge follows the optimal action is needed. The common threshold is supplied by UniformValueConsistency in the formal statement.",
        "equation": "Vₓ − Vₓ₊₁ ≥ κ√Vₓ",
        "ref": "theorem1_part3",
        "marker": "  have hgap"
      },
      {
        "title": "Every edge consumes potential",
        "body": "Apply the square-root difference identity to the lower visit-difference bound. Since the denominator is at most twice the parent square root, each sufficiently large-count edge decreases the square-root quantity by at least a fixed positive amount.\n\nThe total decrease cannot exceed the root value $\\sqrt{n+1}$, because the endpoint square root is nonnegative. Therefore the number of large-count edges is at most a constant times $\\sqrt{n+1}$. Strict decrease bounds the remaining small-count tail by a fixed constant.\n\nThis proves an upper bound for every reached path and hence for a longest path, giving the paper’s bound on $H_{\\max}$. There is no corresponding lower bound for an arbitrary path: some non-optimal paths can end much earlier. The generic $H$ in Lean denotes the chosen path’s depth, so applying the bound to a longest path gives the statement for $H_{\\max}$.",
        "equation": "H(n) ≤ C√(n + 1) + constant",
        "ref": "theorem1_part3",
        "marker": "  obtain"
      }
    ],
    "question": "Why is the result O rather than Θ?",
    "answer": "The proof controls how long any path can be. A particular non-optimal path may be much shorter, so there is no matching lower bound for every path."
  },
  {
    "id": "corollary11",
    "group": "Constant exploration coefficient",
    "title": "Corollary 1.1 · Consecutive suboptimal actions",
    "subtitle": "$A$ path formed by consecutively selecting suboptimal actions with uniformly small priors has length d = O(log log $n$).",
    "result": "d(n) = O(log log n)",
    "assumptions": [
      "Uniform convergence of value estimates and a uniform positive gap lower bound.",
      "Every edge in the chain is suboptimal and cPₐ < Δmin/4.",
      "The root has at most n + 1 arrivals and the endpoint has at least one."
    ],
    "refs": [
      "corollary11",
      "suboptimal_visit_upper_bound"
    ],
    "steps": [
      {
        "title": "Get a contracting square-root recurrence",
        "body": "Let $N_x:=N(s_x)$ along a path formed by consecutively selecting suboptimal actions. Fix $\\varepsilon\\in(0,\\Delta_{\\min}/4)$. Uniform convergence supplies an integer threshold $m_0$, independent of the path, above which every value estimate is within $\\varepsilon$ of its asymptotic value.\n\nThe small-prior assumption gives $cP(s_x,a_x)/(\\Delta(s_x,a_x)-2\\varepsilon)<1/2$. Applying the upper score comparison at the action’s last selection therefore bounds its current count by the larger of the early-count constant and half the square root of $N_x$.\n\nChoose a larger fixed threshold so that the square-root term dominates the early-count constant. Above this threshold, $N_{x+1}\\le\\frac12\\sqrt{N_x}$. Lean uses the corresponding arrival counts, which include the expansion visit and remain positive at a reached endpoint. With these arrival counts, the root is at most $n+1$ and a reached endpoint has at least one arrival.",
        "equation": "Vₓ₊₁ ≤ ½√Vₓ",
        "ref": "corollary11",
        "marker": "  have hrec"
      },
      {
        "title": "Iterate contraction on a logarithmic scale",
        "body": "Split the path at the first count below a fixed threshold, and let $J$ be the length of the preceding prefix. On this prefix, the recurrence $V_{x+1}\\le\\frac12\\sqrt{V_x}$ holds. Every reached arrival count, including the endpoint, is at least one.\n\nLean uses the potential $\\log(\\log(4V))$. Squaring the recurrence gives $(4V_{x+1})^2\\le4V_x$, so taking logarithms twice shows that each edge decreases this potential by at least $\\log2$. The factor four keeps the inner logarithms positive even when an arrival count is one.\n\nSumming the potential decreases telescopes. The endpoint potential has a fixed lower bound, and the root count is at most $n+1$, so the root potential is $O(\\log\\log n)$. This proves the same bound for $J$ without discarding the reached endpoint.",
        "equation": "log log(4Vₓ) − log log(4Vₓ₊₁) ≥ log 2",
        "ref": "corollary11",
        "marker": "  have hsteps"
      },
      {
        "title": "Bound the tail after the threshold",
        "body": "Below the fixed threshold, arrival counts are strictly decreasing positive integers. The number of remaining edges is therefore bounded by a constant independent of the simulation count.\n\nThe finite_chain_cutoff helper returns this tail bound along with the large-count prefix. Adding it to the potential estimate gives $d\\le J+m_0=O(\\log\\log n)$. The proof absorbs the fixed tail into the Big-O constant once $\\log\\log n\\ge1$.\n\nThe small-prior condition is required at every edge in this consecutive suboptimal chain. The recurrence is not applied across intervening optimal actions.",
        "equation": "d ≤ C log log n + bounded tail",
        "ref": "corollary11",
        "marker": "  have htail'"
      }
    ],
    "question": "Does every suboptimal path have this bound without a prior condition?",
    "answer": "This corollary explicitly assumes cPₐ < Δmin/4 at every edge. Its stated result should be read with that condition."
  },
  {
    "id": "integrals",
    "group": "General exploration coefficient",
    "title": "Integral depth estimates",
    "subtitle": "Generalize the square-root potential to a reciprocal-loss integral.",
    "result": "F(v) = ∫₁ᵛ 1/f(m) dm",
    "assumptions": [
      "A decreasing count chain with two-sided step estimates.",
      "Continuity and positivity make the integrals well-defined and ordered.",
      "A bounded endpoint potential, bounded tail, and positive root progress."
    ],
    "refs": [
      "IntegralPath",
      "reciprocal_integral_rectangles",
      "depth_theta_of_integral_path"
    ],
    "steps": [
      {
        "title": "Package the telescoping argument",
        "body": "IntegralPath records exactly the properties needed for a telescoping depth argument. Its root has potential $I(n)$. Along a prefix of length $J$, each edge reduces the potential by at least $\\kappa$ and at most $C$, where both constants are positive and independent of the edge.\n\nTwo kinds of remainder are controlled separately: the endpoint potential is bounded, and the full depth exceeds $J$ by at most a bounded tail. The interface also asks for eventual positive depth and a positive lower bound on $I(n)$, which later allow additive constants to be absorbed.\n\nThis structure does not assert that an arbitrary search has these properties. Subsequent constructions prove them from count identities and one-step estimates, then reuse a single theorem to turn them into $H=\\Theta(I)$.",
        "equation": "κ ≤ F(Vₓ) − F(Vₓ₊₁) ≤ C",
        "ref": "IntegralPath",
        "marker": ""
      },
      {
        "title": "Compare rectangles under a reciprocal curve",
        "body": "For a positive nondecreasing function $f$, its reciprocal is nonincreasing. Rectangle bounds put the integral over $[a,b]$ between $(b-a)/f(b)$ and $(b-a)/f(a)$. Positivity permits division, and continuity supplies interval integrability.\n\nThese endpoint bounds explain how a count interval contributes to a depth potential. For the general continuous schedule theorem, a doubling bound is not assumed: the proof uses a shifted monotone mass and bounds edge integrals directly. The measurable extension instead derives comparisons up to a fixed factor from regular variation.\n\nOnce each large-count edge contributes between two positive constants, summing those integrals counts edges. The endpoint and small-count tail are handled separately before the asymptotic conclusion.",
        "equation": "∫[Vnext,V] dm/f(m) ≍ (V − Vnext)/f(V)",
        "ref": "reciprocal_integral_rectangles",
        "marker": ""
      },
      {
        "title": "Telescope and absorb bounded remainders",
        "body": "Sum the edge-potential bounds over the prefix. The intermediate terms cancel, leaving the root potential $I(n)$ minus the endpoint potential. Use the endpoint bound and the bounded tail to obtain inequalities of the form $\\kappa H\\le I+R$ and $I\\le CH+R$ for a fixed nonnegative $R$.\n\nTo turn these additive estimates into a Theta statement, use the positive lower bound $I\\ge\\delta$. It implies $R\\le\\frac R\\delta I$, so the first inequality gives an upper constant for $H$ in terms of $I$. The condition $H\\ge1$ similarly lets the second inequality absorb $R$ into a multiple of $H$.\n\nThe eventual sandwich theorem then supplies $H=\\Theta(I)$. This final step needs the interface’s positivity conditions; it does not silently assume that $I$ tends to infinity. The same integral comparison is then used for a general exploration coefficient and for parallelism.",
        "equation": "H(n) = Θ(I(n))",
        "ref": "depth_theta_of_integral_path",
        "marker": ""
      },
      {
        "title": "Allow logarithmic corrections for general schedules",
        "body": "For the continuous monotone-mass theorem, the integral over one edge need not have a constant upper bound. The proof instead obtains a constant times $1+\\log(f(V_x)/f(V_{x+1}))$, where $f$ is the shifted saturated mass.\n\nSumming these logarithms cancels the intermediate values. Since the mass is at most the count, its root logarithm is bounded by the logarithm of the root count. The positive child-count fraction then bounds this logarithm by a constant times the number of edges, plus an endpoint constant.\n\nThis yields the same additive depth inequalities used above. The argument is contained in optimal_path_depth_from_integral_steps inside scheduled_puct_depth and is what permits the theorem to omit a doubling hypothesis.",
        "equation": "I(n) ≤ C H(n) + bounded remainder",
        "ref": "scheduled_puct_depth",
        "marker": "  have optimal_path_depth_from_integral_steps"
      }
    ],
    "question": "Why integrate the reciprocal of the loss?",
    "answer": "An edge loses about f(V) visits. Integrating 1/f over that interval assigns roughly one unit of potential per edge, turning root potential into a depth estimate."
  },
  {
    "id": "schedule",
    "group": "General exploration coefficient",
    "title": "General exploration coefficient c(·)",
    "subtitle": "Replace the constant exploration coefficient by a positive function $c(\\cdot)$ of the parent visit count.",
    "result": "F(m) = c(m)√m",
    "assumptions": [
      "c is positive and continuous on [1,∞).",
      "Exploration mass c(m)√m is eventually nondecreasing.",
      "The main uncapped scheduled result also requires a uniform positive optimal prior."
    ],
    "refs": [
      "Assumption.ExplorationSchedule",
      "MCTSModel.Scheduled",
      "ExplorationSchedule.mass",
      "scheduled_puct_depth",
      "scheduled_optimal_share_of_prior"
    ],
    "steps": [
      {
        "title": "Evaluate c at the decision count",
        "body": "In the general exploration setting, the coefficient used at a decision is $c$ evaluated at that state’s current parent selection count. The numerator of the exploration term is therefore the action prior multiplied by $F(m)=c(m)\\sqrt m$.\n\nScheduled retains the same count update laws as Sequential. The change is in its argmax condition, which compares all actions using this count-dependent coefficient. The function $c$ is defined on real numbers, while the natural-number visit count is converted to a real when evaluating it.\n\nIntroducing $F$ keeps later estimates readable: upper bounds on suboptimal visits involve this exploration scale, and depth estimates integrate its reciprocal. Different growth rates of $c$ change how quickly visits are spent away from the optimal path. The paper writes $F(m)=c(m)\\sqrt m$; Lean names this function ExplorationSchedule.mass.",
        "equation": "bonusₐ = Pₐ F(m)/(1 + nₐ)",
        "ref": "MCTSModel.Scheduled",
        "marker": ""
      },
      {
        "title": "Assume monotonicity of the exploration mass",
        "body": "ExplorationSchedule requires positivity and continuity of $c$ on $[1,\\infty)$ and eventual monotonicity of $F(m)=c(m)\\sqrt m$. Its threshold is an explicit positive natural number. It does not require concavity of $c$ or a doubling bound.\n\nMonotonicity controls the exploration mass at earlier selection counts when proving upper visit estimates. For the depth bound, the proof uses a shifted version of the mass and directly bounds the integral over each optimal edge.\n\nThis formulation permits coefficients whose growth is too rapid for a fixed doubling constant. Regular variation supplies additional ratio control only in the corollaries where it is assumed.",
        "equation": "F(m) is eventually nondecreasing",
        "ref": "Assumption.ExplorationSchedule",
        "marker": ""
      },
      {
        "title": "Account for saturation and expansion arrivals",
        "body": "Write $F(m)=c(m)\\sqrt m$. The difference between a parent count and an optimal-child count cannot exceed the available visits. This introduces the analytical scale $g(m)=\\min\\{F(m),m\\}$.\n\nThe continuous-schedule proof uses a regularized, shifted version of this scale: shiftedMass evaluates it at $\\max\\{q,x-2\\}$, where $q$ is a fixed threshold. The shift accounts for selection and arrival counts, while the maximum makes the potential well behaved below the threshold.\n\nTaking the reciprocal of the minimum gives the maximum of $1/F(m)$ and $1/m$, which is comparable to their sum. Integrating therefore produces the exploration integral plus a logarithm. The execution itself still uses the original coefficient $c$.",
        "equation": "g(m) = min(c(m)√m, m)",
        "ref": "scheduled_puct_depth",
        "marker": "  let shiftedMass"
      },
      {
        "title": "Secure an optimal share",
        "body": "The uncapped theorem assumes that optimal-action priors have a common positive lower bound at nonterminal states. Uniformly accurate values and the pUCT score comparisons then force the optimal action to receive a positive fraction of the parent selections at large counts.\n\nTo prove this, compare each suboptimal action at its last selection, use the positive optimal prior in the exploration term, and sum over actions using the normalized priors. The resulting fraction and threshold work uniformly across states.\n\nThis optimal share keeps child counts comparable to parent counts along large-count edges. It also bounds the count at a nonterminal frontier whose optimal child has never been visited. These are the retention and endpoint controls needed in the integral proof.",
        "equation": "n* ≥ θm for some θ > 0",
        "ref": "scheduled_optimal_share_of_prior",
        "marker": ""
      }
    ],
    "question": "Does the algorithm replace c with min(c,√m)?",
    "answer": "No. The capped coefficient is an analytical tool for the depth comparison. The execution’s argmax still uses the original schedule c."
  },
  {
    "id": "theorem2",
    "group": "General exploration coefficient",
    "title": "Theorem 2 · General exploration coefficient",
    "subtitle": "If $c(m)$ = $O(\\sqrt m)$, the maximum depth along the optimal path is given by the integral estimate. If $c(m)$ = $\\Omega(\\sqrt m)$, it is Θ(log $n$). Both hold until capped by a finite terminal depth.",
    "result": "c = O(√m): Hₒₚₜ = Θ(∫₁ⁿ dm/[c(m)√m]); c = Ω(√m): Hₒₚₜ = Θ(log n)",
    "assumptions": [
      "Scheduled pUCT; regularity; UniformValueConsistency; a positive continuous coefficient with eventually nondecreasing mass c(m)√m.",
      "A common positive lower bound on optimal priors at nonterminal states.",
      "An uncapped optimal path with root arrivals n + 1."
    ],
    "refs": [
      "theorem2",
      "scheduled_puct_depth",
      "DepthIntegral.saturated",
      "saturated_depth_weak",
      "saturated_depth_strong"
    ],
    "steps": [
      {
        "title": "Prove the stronger depth estimate",
        "body": "The private helper scheduled_puct_depth proves the combined logarithmic and exploration-integral estimate directly from the scheduled search model. It uses positivity, continuity, and eventual monotonicity of $F(m)=c(m)\\sqrt m$; neither concavity nor a doubling hypothesis is needed.\n\nUpper visit estimates and a positive optimal share control the count intervals along the optimal path. A score comparison at an optimal selection supplies a lower gap estimate at that selection. The proof then bounds the integrals across reached edges using the shifted monotone mass, rather than assuming the current count and an earlier selection have comparable exploration masses.\n\nEach sufficiently large edge has a positive lower integral bound. Its upper bound includes a logarithmic correction $C(1+\\log(f(V_x)/f(V_{x+1})))$ for the shifted mass $f$. Those logarithms telescope along the path; the positive child-count share controls the remaining root logarithm by the path length. Controlling the frontier and removing the bounded tail then give the depth estimate. Finally, removing the fixed shift and using the reciprocal-minimum comparison identifies the potential with $\\log n+\\int_1^n 1/(c(m)\\sqrt m)\\,dm$.",
        "equation": "S(n) = log n + I(n),  I(n) = ∫₁ⁿ dm/[c(m)√m]",
        "ref": "scheduled_puct_depth",
        "marker": ""
      },
      {
        "title": "Case c(m) = O(√m)",
        "body": "If $c(m)=O(\\sqrt m)$, then for all sufficiently large $m$ there is a constant $C>0$ with $c(m)\\le C\\sqrt m$. Taking positive reciprocals gives $1/(c(m)\\sqrt m)\\ge1/(Cm)$.\n\nAfter integration, the exploration contribution therefore dominates the logarithmic contribution, up to a constant from the initial interval. Since the exploration integral is nonnegative and grows at least logarithmically, this constant can be absorbed into the asymptotic comparison.\n\nConsequently, the sum of the two contributions has the same order as the exploration integral alone. Applying the stronger depth estimate from the preceding step proves the first case of Theorem 2. Lean records this simplification in saturated_depth_weak.",
        "equation": "c = O(√m) ⇒ Hₒₚₜ(n) = Θ(I(n))",
        "ref": "saturated_depth_weak",
        "marker": ""
      },
      {
        "title": "Case c(m) = Ω(√m)",
        "body": "If $c(m)=\\Omega(\\sqrt m)$, equivalently $\\sqrt m=O(c(m))$, the comparison goes in the other direction. For some fixed $C>0$ and all sufficiently large $m$, the exploration integrand is at most $C/m$.\n\nIts integral is therefore $O(\\log n)$, after absorbing the fixed initial interval. The logarithmic contribution already supplies the matching lower order. Hence the sum of the logarithmic and exploration contributions is $\\Theta(\\log n)$.\n\nApplying the stronger depth estimate gives $H_{\\mathrm{opt}}(n)=\\Theta(\\log n)$, without the upper growth restriction used in the first case. When $c(m)$ is itself comparable to $\\sqrt m$, both comparisons hold and give the same conclusion.",
        "equation": "√m = O(c) ⇒ Hₒₚₜ(n) = Θ(log n)",
        "ref": "saturated_depth_strong",
        "marker": ""
      },
      {
        "title": "Assemble the two conclusions",
        "body": "The two cases now follow from the same general estimate. If $c(m)=O(\\sqrt m)$, use the exploration integral; if $c(m)=\\Omega(\\sqrt m)$, use the logarithmic estimate. Both statements concern the maximum depth reached along the optimal path.\n\nIn Lean, scheduled_puct_depth supplies the general estimate, and theorem2 combines it with the two comparisons. The use of transitivity simply passes from the actual depth to the general expression and then to the appropriate rate.\n\nThe paper states that both estimates hold until capped by a finite terminal depth. The formalization separates that conclusion: theorem2_capped proves eventual arrival at a fixed terminal depth under its stated sufficient conditions.",
        "equation": "⟨the integral estimate, the logarithmic estimate⟩",
        "ref": "theorem2",
        "marker": ""
      }
    ],
    "question": "Why not use only the exploration integral for arbitrarily large c?",
    "answer": "It can grow too slowly or remain bounded. Count loss saturates at the available parent count, producing the logarithmic term in the general depth scale."
  },
  {
    "id": "corollary21",
    "group": "General exploration coefficient",
    "title": "Corollary 2.1 · c(m) = mᵅL(m)",
    "subtitle": "Under the first case of Theorem 2, suppose $c(m)$ = mᵅL($m$), where $L$ is slowly varying. Then $\\alpha$ ≤ 1/2 since $c(m)$ = $O(\\sqrt m)$.",
    "result": "α < ½ ⇒ Hₒₚₜ(n) = Θ(√n / c(n))",
    "assumptions": [
      "Scheduled pUCT, ExplorationSchedule, regularity, uniform value convergence, positive optimal priors, and an uncapped optimal path.",
      "c = O(√m) and c(m) = mᵅL(m).",
      "ContinuousSlowlyVarying L requires positivity, continuity, and L(λm)/L(m) → 1 for every λ > 0."
    ],
    "refs": [
      "corollary21",
      "ContinuousSlowlyVarying",
      "regular_variation_index_le_half",
      "exploration_eq_critical_of_sqrt_form"
    ],
    "steps": [
      {
        "title": "Restrict the exponent",
        "body": "Under the first case of Theorem 2, write $c(m)=m^\\alpha L(m)$ with $L$ positive and slowly varying. The condition $c(m)=O(\\sqrt m)$ gives $m^{\\alpha-1/2}L(m)=O(1)$.\n\nPositivity and slow variation imply $\\alpha\\le1/2$. Indeed, if $\\alpha>1/2$, the positive power cannot remain bounded after multiplication by a slowly varying factor. Lean establishes the required restriction by comparing the growth across repeated doublings.\n\nThe ratio $c(2m)/c(m)$ tends to $2^\\alpha$. If this limit exceeded $\\sqrt2$, iterating a slightly smaller lower ratio would contradict the assumed square-root upper bound. This proves the exponent restriction before considering the two cases below. Lean uses ContinuousSlowlyVarying here. The separate SlowlyVarying structure requires measurability instead of continuity and is used in Corollary 2.3.",
        "equation": "α ≤ ½",
        "ref": "regular_variation_index_le_half",
        "marker": ""
      },
      {
        "title": "Below the critical exponent",
        "body": "If $\\alpha<1/2$, then $1/L$ is slowly varying. The paper applies Karamata’s theorem to the exploration integral and obtains $\\int_1^n\\frac{\\mathrm{d}m}{m^{\\alpha+1/2}L(m)}=\\Theta(n^{1/2-\\alpha}/L(n))=\\Theta(\\sqrt n/c(n))$.\n\nApplying Theorem 2 proves the first part of the corollary. The condition $\\alpha<1/2$ places the integrand in the range where its integral has this endpoint order; it is the strict inequality that matters for this comparison.\n\nLean proves the particular integral estimate directly. Monotonicity gives a lower bound over a fixed fraction of the interval, while a doubling and halving comparison controls the upper bound. The resulting estimate is the same one used by the paper’s appeal to Karamata’s theorem. The formal corollary derives the search-depth estimate internally from theorem2; its public inputs are the execution, coefficient hypotheses, and path identities.",
        "equation": "Hₒₚₜ(n) = Θ(n½⁻ᵅ/L(n))",
        "ref": "corollary21",
        "marker": "  have hhalving"
      },
      {
        "title": "At the critical exponent",
        "body": "If $\\alpha=1/2$, substitute $c(m)=\\sqrt m\\,L(m)$ into the first case of Theorem 2. The denominator becomes $c(m)\\sqrt m=mL(m)$, so $H_{\\mathrm{opt}}(n)=\\Theta(\\int_1^n\\frac{\\mathrm{d}m}{mL(m)})$.\n\nAt this boundary, the strict exponent inequality used in the preceding integral estimate is unavailable. The integral is therefore retained, and its growth depends on the slowly varying factor $L$.\n\nIn particular, $L(m)=\\Theta(1)$ yields logarithmic depth. Both cases inherit the finite terminal cap from Theorem 2. The additional assumption $c(m)=O(\\sqrt m)$ remains in force throughout Corollary 2.1, so the logarithmic contribution does not need to be retained separately.",
        "equation": "Hₒₚₜ(n) = Θ(∫₁ⁿ dm/[mL(m)])",
        "ref": "exploration_eq_critical_of_sqrt_form",
        "marker": ""
      }
    ],
    "question": "Where does this corollary obtain the search-depth bound?",
    "answer": "It invokes theorem2 internally using the scheduled search execution and path hypotheses. No separate depth estimate is required from the caller."
  },
  {
    "id": "corollary22",
    "group": "General exploration coefficient",
    "title": "Corollary 2.2 · Three exploration regimes",
    "subtitle": "Regular variation and eventual monotonicity of $c(m)\\sqrt m$ classify depth across all exponents $\\alpha\\ge-1/2$.",
    "result": "α ≥ −½",
    "assumptions": [
      "Scheduled pUCT, ExplorationSchedule, regularity, uniform value convergence, positive optimal priors, and an uncapped optimal path.",
      "c(m) = mᵅL(m), with ContinuousSlowlyVarying L.",
      "There is no c = O(√m) assumption and no concavity requirement."
    ],
    "refs": [
      "corollary22",
      "regular_variation_of_schedule",
      "ContinuousSlowlyVarying",
      "corollary22_capped"
    ],
    "steps": [
      {
        "title": "Monotone mass restricts the exponent",
        "body": "Write $F(m)=c(m)\\sqrt m=m^{\\alpha+1/2}L(m)$. Eventual monotonicity implies $F(2m)/F(m)\\ge1$ for sufficiently large $m$. Slow variation makes this ratio converge to $2^{\\alpha+1/2}$.\n\nThe limit is therefore at least one, giving $\\alpha\\ge-1/2$. There is no upper restriction on the exponent. In particular, the theorem applies to decreasing coefficients when their exploration mass remains nondecreasing.\n\nThe helper regular_variation_of_schedule also compares $c$ with the square-root scale on either side of the critical exponent. These comparisons are derived from the hypotheses; a depth estimate is not an extra input.",
        "equation": "α ≥ −½",
        "ref": "regular_variation_of_schedule",
        "marker": ""
      },
      {
        "title": "Classify the two strict regimes",
        "body": "For $\\alpha<1/2$, the coefficient is $O(\\sqrt m)$, so Corollary 2.1 gives $H_{\\mathrm{opt}}(n)=\\Theta(\\sqrt n/c(n))$. Its endpoint case $\\alpha=-1/2$ is included when the schedule assumptions hold.\n\nFor $\\alpha>1/2$, the coefficient dominates the square-root scale. The logarithmic case of Theorem 2 gives $H_{\\mathrm{opt}}(n)=\\Theta(\\log n)$.\n\nThe Lean proof obtains both coefficient comparisons from regular_variation_of_schedule, then composes the corresponding depth results. Uniform convergence, positive optimal priors, and the uncapped path assumptions remain in force.",
        "equation": "α < ½: Θ(√n/c(n));  α > ½: Θ(log n)",
        "ref": "corollary22",
        "marker": "  have hdepth"
      },
      {
        "title": "Retain both contributions at the boundary",
        "body": "At $\\alpha=1/2$, substituting $c(m)=\\sqrt m\\,L(m)$ changes the exploration integrand to $1/(mL(m))$. The general estimate therefore retains the sum of this integral and $\\log n$.\n\nUnlike Corollary 2.1, there is no square-root upper bound on the coefficient here. The integral need not dominate the logarithm, so dropping the logarithmic term would lose an essential contribution.\n\nThe capped counterpart derives eventual equality with a fixed depth $D$ and returns each comparison with its rate replaced by the minimum of that rate and $D$.",
        "equation": "α = ½: Θ(log n + ∫₁ⁿ dm/[mL(m)])",
        "ref": "corollary22",
        "marker": "  exact (exploration_eq"
      }
    ],
    "question": "Does this classification require a concave coefficient?",
    "answer": "No. It requires a positive continuous coefficient whose exploration mass is eventually nondecreasing, together with continuous slow variation. The exponent satisfies α ≥ −1/2, with no upper bound."
  },
  {
    "id": "corollary23",
    "group": "General exploration coefficient",
    "title": "Corollary 2.3 · Measurable exploration schedules",
    "subtitle": "Replace continuity and monotonicity by measurable slow variation and local boundedness, for $\\alpha>-1/2$.",
    "result": "α > −½",
    "assumptions": [
      "Scheduled pUCT, regularity, uniform value convergence, positive optimal priors, and an uncapped optimal path.",
      "c(m) = mᵅL(m), α > −1/2, and SlowlyVarying L.",
      "Both c and 1/c are bounded on each compact interval [1,b]."
    ],
    "refs": [
      "corollary23",
      "SlowlyVarying",
      "LocallyBounded",
      "Assumption.GeneralExplorationSchedule",
      "corollary23_capped"
    ],
    "steps": [
      {
        "title": "Use measurable slow variation",
        "body": "SlowlyVarying requires $L$ to be positive on $[1,\\infty)$, almost-everywhere measurable for restricted Lebesgue measure, and to satisfy $L(\\lambda m)/L(m)\\to1$ for every fixed $\\lambda>0$. Unlike ContinuousSlowlyVarying, it does not require continuity.\n\nCorollary 2.3 assumes $c(m)=m^\\alpha L(m)$ with $\\alpha>-1/2$. It retains the scheduled search execution, regularity, uniform value convergence, positive optimal priors, and optimal-path count identities.\n\nThe conclusion has the same three regimes as Corollary 2.2. The strict lower exponent bound is essential to the positive-index growth argument used here; this theorem does not cover $\\alpha=-1/2$.",
        "equation": "α > −½",
        "ref": "SlowlyVarying",
        "marker": ""
      },
      {
        "title": "Control compact intervals",
        "body": "LocallyBounded means that the image of every interval $[1,b]$ is bounded. The theorem requires this for both $c$ and $1/c$, so the positive coefficient cannot have unbounded spikes or approach zero without a bound on such intervals.\n\nMeasurability together with the bound on $1/c$ makes the reciprocal exploration mass integrable on compact intervals. The finite contribution below a fixed threshold can then be absorbed in the asymptotic estimates.\n\nAll integrals use Lebesgue measure. These assumptions replace the compact-interval control that continuity supplied in the preceding corollaries.",
        "equation": "F(m) = c(m)√m",
        "ref": "LocallyBounded",
        "marker": ""
      },
      {
        "title": "Recover comparisons without monotonicity",
        "body": "The exploration mass has regular-variation index $\\rho=\\alpha+1/2>0$. The proof derives eventual growth and comparison bounds from measurable slow variation. In particular, earlier masses are bounded by a fixed multiple of later masses, and masses at a fixed ratio of counts are comparable.\n\nThese facts are packaged internally in GeneralExplorationSchedule together with interval integrability. They tolerate oscillations while still supporting the upper count bounds and the lower bounds transferred from an optimal selection.\n\nThe helper constructions are local to corollary23. The caller supplies slow variation and local boundedness, not a general schedule object or a pre-proved depth estimate.",
        "equation": "F(x) ≤ A F(y) for sufficiently large x ≤ y",
        "ref": "corollary23",
        "marker": "  have regularlyVarying_almost_monotone"
      },
      {
        "title": "Derive depth and classify its rate",
        "body": "The proof builds the path-integral estimate from the scheduled execution and the derived mass comparisons. Integrating over each large-count edge gives bounded positive increments; telescoping and the frontier bound give the combined logarithmic and exploration-integral rate.\n\nFor $-1/2<\\alpha<1/2$, the exploration integral has order $\\sqrt n/c(n)$. At $\\alpha=1/2$, retain $\\log n+\\int_1^n 1/(mL(m))\\,dm$. For $\\alpha>1/2$, the logarithm determines the depth rate.\n\nThe public theorem returns these three implications. Its capped counterpart proves the corresponding minimum-with-depth comparisons from capped paths; eventual arrival at the cap is established inside that proof.",
        "equation": "α < ½: Θ(√n/c(n));  α > ½: Θ(log n)",
        "ref": "corollary23",
        "marker": "  have hdepth"
      }
    ],
    "question": "Can a discontinuous exploration coefficient satisfy this theorem?",
    "answer": "Yes, if its slowly varying factor satisfies the measurability and ratio conditions, α > −1/2, and both c and 1/c are locally bounded. The search and path hypotheses still apply."
  },
  {
    "id": "parallel-model",
    "group": "Parallelism",
    "title": "Tree-parallel MCTS",
    "subtitle": "Distinguish decisions made, snapshots seen, and work actually completed.",
    "result": "visible ≤ issued; completed ≤ issued",
    "assumptions": [
      "Each state has at least one thread.",
      "Snapshot lag and outstanding work are bounded by the thread count.",
      "Argmax uses visible counts; reported tree paths use completed counts.",
      "Value estimates stabilize uniformly as visible parent counts grow."
    ],
    "refs": [
      "MCTSModel.ParallelExecution",
      "parallel_issued_gap_upper",
      "parallel_completed_gap_upper",
      "parallel_visit_bounds",
      "Assumption.CompletedContention"
    ],
    "steps": [
      {
        "title": "Track three kinds of counts",
        "body": "A parallel decision can use counts that are older than the work already issued, and some issued work may not yet have completed. The execution model therefore tracks issued selections, visible snapshots, and completed counts separately.\n\nThe pUCT argmax comparison uses visibleParent and visibleChild, because those are the statistics available to the selecting thread. M’s update counters track issued selections. Completed child counts determine the reported tree, and their sum gives the completed parent count.\n\nThe assumptions bound snapshot lag and outstanding work by the number of threads. These bounds justify converting estimates from the statistics used at selection to the counts used to measure depth. A worker-count bound alone is not substituted for the explicit lag and accuracy conditions in the model.",
        "equation": "issued − visible ≤ T; issued − completed ≤ T",
        "ref": "MCTSModel.ParallelExecution",
        "marker": ""
      },
      {
        "title": "Carry lag through the score argument",
        "body": "Repeat the selection-score argument using the visible counts at the relevant decision. To relate that comparison to a later reported tree, first compare visible counts with issued counts and then compare issued counts with completed counts.\n\nEach conversion introduces an error controlled by $T$. After using the uniform value estimates and summing over the bounded action set, the upper difference has size at most $C$ times $\\sqrt V+T$. The lower estimate has a positive square-root term with deductions ET and $R$, representing the thread-dependent and fixed errors.\n\nThese inequalities are derived from the execution assumptions. parallelEstimates_of_execution packages them into a convenient interface for the path proof. In particular, the square-root estimates are not separately assumed as part of ParallelExecution.",
        "equation": "B√V − ET − R ≤ V − Vnext ≤ C(√V + T)",
        "ref": "parallel_visit_bounds",
        "marker": ""
      },
      {
        "title": "State the thread contention assumption",
        "body": "The paper’s thread contention assumption describes a stale selection window in which at least $\\rho T$ overlapping selections reach a node, but at most $K$ select the optimal action. This leaves at least $\\rho T-K$ suboptimal selections in that group.\n\nLean’s CompletedContention records corresponding increments of the issued parent and action counts between two times. It also requires that the group’s action increments are included in the completed counts at the reported observation. Without this completion requirement, issued suboptimal work would not yet justify a lower bound on the measured tree’s counts.\n\nSumming the completed suboptimal contributions yields a lower bound proportional to $T$ once $T$ is large enough to absorb $K$. This is the additional source of loss needed when the thread count is too large for the square-root estimate alone to give a useful lower bound.",
        "equation": "completed nonoptimal selections ≥ ρT − K",
        "ref": "Assumption.CompletedContention",
        "marker": ""
      }
    ],
    "question": "Why not identify issued counts with the reported tree?",
    "answer": "Some issued simulations may still be running. The model bounds this discrepancy explicitly and states depth results using completed counts."
  },
  {
    "id": "lemma4",
    "group": "Parallelism",
    "title": "Lemma 4 · One-step estimates under parallelism",
    "subtitle": "Combine square-root exploration loss with a contention contribution proportional to threads.",
    "result": "V − Vnext = Θ(√V + T), under contention",
    "assumptions": [
      "c > 0; ParallelExecution; Regularity; reached optimal path identities.",
      "The upper and sufficiently small-thread bounds do not require contention.",
      "The general combined lower bound uses CompletedContention at observed path nodes."
    ],
    "refs": [
      "lemma4",
      "lemma4_of_visit_bounds",
      "parallelEstimates_of_execution"
    ],
    "steps": [
      {
        "title": "Keep the unconditional upper bound",
        "body": "Let $a_i\\ne a^*(s_x)$ be a suboptimal action and write $n_i=N(s_x,a_i)$. At a selection of $a_i$, denote the visible parent and action counts by $\\bar m$ and $\\bar n_i$. The pUCT comparison gives the same square-root upper estimate as in Theorem 1(1).\n\nThe visible counts lag the issued counts by at most $T$, and outstanding work is bounded by $T$. Converting to the counts at the reported observation therefore adds a term of order $T$. The parent visible count is also no larger than the appropriate issued parent count, whose difference from the completed parent count is controlled.\n\nSumming over the at most $b-1$ suboptimal actions yields the one-step upper bound of order $\\sqrt{N_x}+T$. Lean carries this out with completed arrival counts $V_x$, absorbing the single expansion visit into the upper constant.",
        "equation": "V − Vnext ≤ C(√V + T)",
        "ref": "lemma4",
        "marker": ""
      },
      {
        "title": "When threads are small, absorb their errors",
        "body": "We next prove the sequential lower part. Choose a suboptimal action whose prior is bounded below along the optimal path, as guaranteed by regularity. Repeating the lower-bound argument of Theorem 1(1), while allowing the bounded lag, gives a square-root term minus a term proportional to $T$ and a fixed constant.\n\nLean packages this as $B\\sqrt V-ET-R$. If $T\\le\\eta\\sqrt V$ for sufficiently small $\\eta>0$, the term $ET$ consumes only a fixed fraction of $B\\sqrt V$. For sufficiently large $V$, the fixed $R$ is also absorbed.\n\nThe remaining lower bound is $c_0\\sqrt V$ for some $c_0>0$. This proves the small-thread part without contention: the error from stale and outstanding selections is small enough compared with the sequential square-root contribution.",
        "equation": "T ≤ η√V ⇒ V − Vnext ≥ c₀√V",
        "ref": "lemma4",
        "marker": "    refine ⟨B / 2"
      },
      {
        "title": "When threads are large, use thread contention",
        "body": "Finally, assume the contention conditions. In the stale selection window, at least $\\rho T$ selections reach the state and at most $K$ select the optimal action. Hence at least $\\rho T-K$ select suboptimal actions.\n\nThe paper measures the tree after the simulations have completed their backups. Lean requires explicitly that the selected group’s increments are included in the completed counts at the observation. These suboptimal selections therefore contribute to the measured parent-to-optimal-child difference.\n\nFor $T\\ge2K/\\rho$, we have $\\rho T-K\\ge(\\rho/2)T$. Thus the linear lower bound holds with $c_1=\\rho/2$. This argument is additional to the small-thread estimate and supplies the lower bound when the thread contribution is large.",
        "equation": "V − Vnext ≥ ρT − K",
        "ref": "lemma4",
        "marker": "  have hcontention"
      },
      {
        "title": "Combine the two regimes",
        "body": "Combining the lower bounds gives the two-sided one-step estimate. If $T\\le\\eta\\sqrt{N_x}$, the sequential lower bound implies $N_x-N_{x+1}=\\Omega(\\sqrt{N_x}+T)$, because the thread term is bounded by a multiple of the square-root term.\n\nIf $T>\\eta\\sqrt{N_x}$ and $T$ is sufficiently large, the contention lower bound gives $N_x-N_{x+1}=\\Omega(T)=\\Omega(\\sqrt{N_x}+T)$. The remaining bounded-count cases can be included in a fixed threshold and a constant-depth tail.\n\nChoose positive constants that work in both regimes and combine the result with the one-step upper bound. Lean’s lemma4_of_visit_bounds performs this combination and supplies constants uniform over the observed path nodes.",
        "equation": "κ₁(√V + T) ≤ V − Vnext ≤ κ₂(√V + T)",
        "ref": "lemma4_of_visit_bounds",
        "marker": ""
      }
    ],
    "question": "Is the Θ(√V + T) loss law unconditional?",
    "answer": "No. Its general lower bound requires completed contention. The upper bound and a small-thread square-root lower bound do not."
  },
  {
    "id": "theorem3",
    "group": "Parallelism",
    "title": "Theorem 3 · Constant parallelism",
    "subtitle": "Consider tree-parallel MCTS with a constant exploration coefficient $c>0$ and a fixed number $T$ of concurrent threads. The asymptotic depth remains $\\Theta(\\sqrt n)$, until capped by a finite terminal depth.",
    "result": "Hₒₚₜ(n,T) = Θ(√n) for fixed T",
    "assumptions": [
      "c > 0; ParallelExecution; Regularity.",
      "T is fixed along the sequence of simulation counts and along the path.",
      "The reached optimal path and its deepest reached node use completed counts, with root arrivals n + 1.",
      "No CompletedContention hypothesis is required."
    ],
    "refs": [
      "theorem3",
      "parallel_frontier_bound",
      "parallel_frontier_depth_from_steps",
      "parallel_rate_small"
    ],
    "steps": [
      {
        "title": "Fixed thread errors eventually become small",
        "body": "Let $s_x$ denote the node at depth $x$ on the optimal path and let $N_x:=N(s_x)$. Since $T$ is fixed, the staleness error caused by in-flight simulations is $O(1)$.\n\nBy the same argument as in Lemma 4, the sequential one-step estimate is perturbed by at most an additive constant depending on $T$. Hence, for all sufficiently large $N_x$, the difference $N_x-N_{x+1}$ is bounded above and below by positive multiples of $\\sqrt{N_x}$.\n\nThe finitely many levels below this fixed threshold contribute only $O(1)$ additional depth. This is why no contention hypothesis is required here: for fixed $T$, the thread-dependent error is eventually dominated by the square-root term. Both the constants and the count threshold may depend on the fixed thread count. ParallelExecution makes the snapshot-lag, outstanding-work, and uniform value-convergence conditions explicit.",
        "equation": "V − Vnext = Θ(√V + T) for fixed T",
        "ref": "theorem3",
        "marker": "    have hstep_data"
      },
      {
        "title": "Bound the omitted integral",
        "body": "We now apply the same Riemann-sum comparison used in Theorem 1. Since $m\\mapsto m^{-1/2}$ is decreasing, $(N_x-N_{x+1})/\\sqrt{N_x}$ is at most the integral over $[N_{x+1},N_x]$.\n\nUsing the lower one-step bound and summing along the optimal path gives an upper depth bound of order $\\int_1^n\\frac{\\mathrm{d}m}{\\sqrt m}=O(\\sqrt n)$. For the reverse bound, the upper one-step estimate ensures that each sufficiently large-count step contributes at most a constant amount to this integral.\n\nLean uses the parallel integral with denominator $\\sqrt m+T$ and separately bounds the omitted part below the deepest reached node. Since that endpoint has $O(T)$ arrivals and the integrand is at most $1/T$, the omitted integral is $O(1)$. For fixed $T$, this gives the same asymptotic comparison.",
        "equation": "H + 1 = Θ(∫₁ⁿ dm/(√m + T))",
        "ref": "theorem3",
        "marker": "    obtain ⟨A"
      },
      {
        "title": "Simplify for constant T",
        "body": "The integral is $\\Theta(\\sqrt n)$. The upper depth estimate gives $H_{\\mathrm{opt}}(n,T)=O(\\sqrt n)$, while the reverse integral comparison gives $H_{\\mathrm{opt}}(n,T)=\\Omega(\\sqrt n)$. Combining the two bounds yields the statement of Theorem 3.\n\nIn Lean, the intermediate parallel rate is $n/(\\sqrt n+T)$, which is $\\Theta(\\sqrt n)$ for fixed $T$. The proof initially estimates $H+1$ to include a path consisting only of the root, and then proves $H\\ge1$ eventually before replacing $H+1$ with $H$.\n\nFinally, the root arrival count is $n+1$ for $n$ completed simulations. The comparison between $\\sqrt{n+1}$ and $\\sqrt n$ removes this fixed indexing difference. A finite terminal depth is handled by theorem3_capped.",
        "equation": "n/(√n + T) = Θ(√n)",
        "ref": "theorem3",
        "marker": "    have hsmall"
      }
    ],
    "question": "Why can Theorem 3 omit contention?",
    "answer": "For fixed T, the adverse thread terms are bounded constants. At sufficiently large counts the square-root exploration lower bound dominates them."
  },
  {
    "id": "theorem4",
    "group": "Parallelism",
    "title": "Theorem 4 · General parallelism",
    "subtitle": "Consider tree-parallel MCTS with $T$ = $T(n)$ concurrent threads and $T(n)=o(n)$, under regularity and thread contention. The integral estimate gives the asymptotic depth until capped by a finite terminal depth.",
    "result": "Hₒₚₜ(n,T) = Θ(∫₁ⁿ dm/(√m + T))",
    "assumptions": [
      "The parallel execution and regularity assumptions.",
      "Thread contention is formalized by CompletedContention at each reported path observation, including the requirement that the selected group is counted as completed.",
      "Eventually T(n) ≥ 1, and T(n) = o(n).",
      "The reached path has root arrivals n + 1; before the terminal cap, the optimal child at the deepest reached node has zero completed visits."
    ],
    "refs": [
      "theorem4",
      "parallel_integral_theta_rate",
      "parallel_frontier_depth_from_steps",
      "lemma4"
    ],
    "steps": [
      {
        "title": "Get uniform two-sided edge bounds",
        "body": "Let $s_x$ be the node at depth $x$ on the optimal path, let $N_x:=N(s_x)$, and write $D_x:=N_x-N_{x+1}$. By Lemma 4, there are constants $0<\\kappa_1\\le\\kappa_2$ such that $D_x$ is bounded above and below by these multiples of $\\sqrt{N_x}+T$ above a fixed threshold.\n\nDefine $\\Phi_T(u):=\\int_1^u\\frac{\\mathrm{d}m}{\\sqrt m+T}$. Since the integrand is decreasing, the lower one-step estimate gives a positive lower bound on the integral over every reached large-count edge.\n\nSumming over the optimal path yields the upper depth estimate in terms of $\\Phi_T(n)$. For the reverse comparison, the proof must also bound each edge integral above and control the integral omitted below the deepest reached node. Lean obtains the step bounds from the completed-contention hypothesis at the reported observations.",
        "equation": "κ(√V + T) ≤ V − Vnext ≤ C(√V + T)",
        "ref": "theorem4",
        "marker": "    obtain ⟨κ"
      },
      {
        "title": "Bound visits at the deepest reached node",
        "body": "Before the terminal cap is reached, the optimal child at the deepest reached node has zero visits. The one-step upper bound therefore gives a count of order $T$ at that node. Bounded counts are also covered since $T\\ge1$.\n\nThe omitted integral is bounded by the endpoint count divided by $T$, because $1/(\\sqrt m+T)\\le1/T$. Hence this part contributes only $O(1)$ even when the endpoint count grows with $T$.\n\nLean also uses $T(n)=o(n)$ to establish eventual positive depth. Otherwise the deepest reached node would still be the root, forcing its $n+1$ arrivals to be $O(T(n))$, a contradiction. This permits the intermediate comparison for $H+1$ to be converted into one for $H$.",
        "equation": "Vₕ ≤ AT;  T = o(n) ⇒ H ≥ 1 eventually",
        "ref": "theorem4",
        "marker": "    have hprogress"
      },
      {
        "title": "Compare the integral to a simple rate",
        "body": "For the reverse integral comparison, first consider an edge whose difference satisfies $D_x\\le N_x/2$. The child count is then at least half the parent count, so monotonicity and the upper one-step bound give a constant upper bound on the edge integral.\n\nIf $D_x>N_x/2$, the same upper bound forces $N_x=O(T)$ above a fixed threshold: a large fraction of $N_x$ cannot be bounded by $\\sqrt{N_x}+T$ unless the thread term is sufficiently large. The integral is then at most $N_x/T=O(1)$.\n\nSumming these bounds and adding the omitted endpoint integral gives the lower depth estimate. Thus $H_{\\mathrm{opt}}(n,T)=\\Theta(\\int_1^n\\frac{\\mathrm{d}m}{\\sqrt m+T})$. Lean also proves that this integral is comparable to $n/(\\sqrt n+T)$, with $T=T(n)$ held fixed during integration.",
        "equation": "∫₁ⁿ dm/(√m + T(n)) = Θ(n/(√n + T(n)))",
        "ref": "parallel_integral_theta_rate",
        "marker": ""
      },
      {
        "title": "Read the two asymptotic regimes",
        "body": "If $T=o(\\sqrt n)$, the integral is at most $\\int_1^n\\mathrm{d}m/\\sqrt m=O(\\sqrt n)$. For a lower bound, on the interval from $T^2$ to $n$ the denominator is at most $2\\sqrt m$, giving $\\sqrt n-O(T)=\\Theta(\\sqrt n)$.\n\nIf $T\\gg\\sqrt n$, meaning $\\sqrt n=o(T)$, then $\\sqrt m/T\\le\\sqrt n/T=o(1)$ uniformly for $1\\le m\\le n$. Thus $\\sqrt m+T=(1+o(1))T$ throughout the interval, and the integral is $\\Theta(n/T)$.\n\nApplying the integral depth estimate gives the two regimes in the paper. The standing assumption $T(n)=o(n)$ is still required; the theorem does not extend this conclusion to a thread count proportional to the total simulation count. The separate theorem4_capped proves eventual arrival at a fixed terminal depth without a contention assumption.",
        "equation": "T ≪ √n: Θ(√n);  √n ≪ T: Θ(n/T)",
        "ref": "theorem4",
        "marker": "  have hrate"
      }
    ],
    "question": "Does the theorem cover T proportional to n?",
    "answer": "No. The statement assumes T = o(n). That condition is used to prove root progress and is part of the result’s scope."
  }
];
