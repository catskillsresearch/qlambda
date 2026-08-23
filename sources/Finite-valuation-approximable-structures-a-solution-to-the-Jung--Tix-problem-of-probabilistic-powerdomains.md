# Finite-valuation approximable structures: a solution to the Jung–Tix problem of probabilistic powerdomains

Yuxu Chen, Hui Kou, Zhenchao Lyu  
School of Mathematics, Sichuan University  
arXiv:2608.03073v1 [cs.LO] 4 Aug 2026

Plain-text extraction of `Finite-valuation-approximable-structures-a-solution-to-the-Jung--Tix-problem-of-probabilistic-powerdomains.pdf` (`pdftotext -layout`). Not a substitute for the PDF.

The authors state that a Lean 4 formalization will be released at  
<https://github.com/ChanYuxu/Recent-Progress-on--Domain-Theory>.

---

                                        Finite-valuation approximable structures: a solution to the Jung–Tix
                                                      problem of probabilistic powerdomains⋆
                                                                          Yuxu Chena , Hui Koua , Zhenchao Lyua
                                                          a
                                                              School of Mathematics, Sichuan University, Chengdu, P.R. China, 610065




                                        Abstract
                                        We introduce the category ωFVA of finite-valuation approximable domains, a full subcategory of
                                        continuous domains contained in the category of pointed countably based FS-domains. We prove
                                        that ωFVA is Cartesian closed and closed under both the subprobability and probability valuation
                                        powerdomains. Hence the valuation monads V≤1 and V1 restrict to ωFVA, yielding a positive
arXiv:2608.03073v1 [cs.LO] 4 Aug 2026




                                        answer to the generalized form of Jung–Tix problem, one of the longest-standing open problem
                                        in domain theory since 1990s. The proof is divided into two steps. First, for every finite poset P,
                                        we construct an increasing FS approximate identity on V≤1 (P), and thereby show that V≤1 (P) is
                                        a countably based FS-domain. Second, we call a domain finite-valuation approximable when its
                                        identity is the pointwise supremum of an increasing sequence of maps factoring through spaces
                                        V≤1 (Pn ), where each Pn is finite. A finite-separation saturation theorem and a unified kernel-lifting
                                        theorem then show that ωFVA is closed under Scott-continuous retracts, finite products, function
                                        spaces, V≤1 , and V1 .
                                        Keywords: domain theory, FS-domain, finite-valuation approximate identity, continuous valuation,
                                        probabilistic powerdomain, Cartesian-closed category
                                        2020 MSC: 06B35, 06F30, 18D15, 68Q55, 60B05



                                        1. Introduction
                                            Domain theory originated in Dana Scott’s order-theoretic approach to computation and in the
                                        Scott–Strachey programme for denotational semantics [18–20]. Its basic idea is to order partial
                                        objects by information content: x ≤ y means that y contains at least the information present in x.
                                        Directed suprema describe limits of compatible approximations, Scott-continuous maps preserve
                                        those limits, and least fixed points interpret recursive definitions. Suitable Cartesian closed classes
                                        of domains then provide interpretations of higher-order function types. Domain theory thereby
                                        connects order, topology, fixed-point theory, and the semantics of programming languages within a
                                        single mathematical setting [1, 4].

                                          ⋆
                                           Research supported by NSF of China (Nos. 12471439, 12231007).
                                           Email addresses: chenyuxu@scu.edu.cn (Yuxu Chen), kouhui@scu.edu.cn (Hui Kou),
                                        zhenchaolyu@scu.edu.cn (Zhenchao Lyu)


---

     Finite order structure has played an organizing role from the beginning. Scott’s universal
domain Pω represents data types by retracts of an algebraic domain whose compact elements are
finite [21]. Plotkin’s universal domain Tω and the embedding–projection method of Smyth and
Plotkin similarly reconstruct infinite domains and solutions of recursive domain equations from
controlled approximation stages [16, 22]. Jung’s systematic study of Cartesian closed categories
of domains placed bifinite domains, their Scott-continuous retracts, the RB-domains, and the
broader class of FS-domains at the centre of this finite-approximation programme [1, 11]. In
particular, FS-domains form one of the principal Cartesian closed classes of pointed domains with
all Scott-continuous maps as morphisms. The structure of these classes and their order-topological
foundations were subsequently developed further by Lawson, Scott, and their collaborators [4].
     The introduction of probabilistic computation revealed a persistent obstruction to this pro-
gramme. Jones and Plotkin introduced the probabilistic powerdomain in order to model proba-
bilistic choice [9, 10]. For a dcpo D, let V≤1 (D) and V1 (D) denote, respectively, the dcpos of
continuous subprobability and probability valuations on D, ordered pointwise on Scott-open sets.
The valuation construction preserves continuity under standard hypotheses, but the class of all
continuous domains is not Cartesian closed. Conversely, the standard Cartesian closed subclasses
defined by strong finite-approximation properties are not known in general to be preserved by
probabilistic powerdomains. Thus the two structures required for a direct higher-order probabilistic
semantics, namely function-space exponentials and probabilistic powerdomains, do not automati-
cally coexist. Jung and Tix proved that V≤1 (P) is an RB-domain for finite rooted trees P and an
FS-domain for finite reversed rooted trees P [13]. They emphasized, however, that these finite-tree
results illustrate the difficulty rather than provide a satisfactory general answer. The resulting
Jung–Tix compatibility problem asks whether one can reconcile probabilistic powerdomains with
the function-space constructions of domain theory.
     Several important advances have clarified why the problem is difficult. Goubault-Larrecq
introduced ω-QRB-domains and proved that they are preserved by the probabilistic powerdomain,
finite products, retracts, and expanding bilimits, but the resulting category is not Cartesian closed [5].
Goubault-Larrecq and Jung subsequently proved that QRB-domains coincide with QFS-domains
and with Lawson-compact quasicontinuous dcpos, and established the corresponding probabilistic
closure theorem without the earlier countability and pointedness restrictions [7]. Lyu and Kou also
studied the probabilistic powerdomain from a topological viewpoint [15]. Passing from continuous
to quasicontinuous domains does not remove this obstruction within the full-subcategory setting.
Jia, Jung, Kou, Li, and Zhao proved that every full Cartesian closed subcategory of the category of
quasicontinuous domains and Scott-continuous maps consists entirely of continuous domains [8].
Thus a full Cartesian closed solution cannot be obtained merely by enlarging the object class from
continuous to quasicontinuous domains.
     The obstruction is already visible on finite posets. Even for finite posets, it is difficult to check if
their probabilistic powerdomains are FS-domains. For nearly three decades, the Jung–Tix problem
has become one of the central and technically most difficult open problems in domain theory. Its
resolution is fundamental to the development of a satisfactory domain-theoretic foundation for
higher-order probabilistic denotational semantics.
     In this paper, we give a positive answer to the Jung–Tix problem by introducing ωFVA, a
Cartesian closed full subcategory consisting of continuous domains that is closed under probabilistic
                                                     2


---

powerdomains.
    The proof is divided into two stages. First, we treat finite poset. We prove that the probabilistic
powerdomain of every finite poset is an FS-domain. The second stage is to use the finite valuation
spaces themselves as building blocks for general domains. A domain is called finite-valuation
approximable when its identity is the pointwise supremum of an increasing sequence of maps,
each factoring through V≤1 (Pn ) for some finite poset Pn . We write ωFVA for the resulting full
subcategory. Here “finite” refers to Pn ; the factorization object V≤1 (Pn ) is usually infinite, but
its order is controlled by finitely many upper-set coordinates. Thus the definition relaxes the
finite-image condition of RB-domains while retaining finite order data at every approximation
stage.
    Our main result shows that every object of ωFVA is a pointed countably based FS-domain,
and that ωFVA contains the terminal dcpo and is closed under Scott-continuous retracts, finite
products, function spaces, and both V≤1 and V1 . Consequently, ωFVA is a full Cartesian closed
subcategory of DCPO, and the subprobability and probability valuation monads restrict to it. This
gives a nontrivial finite-structure solution to the category-existence form of the Jung–Tix problem.
    The class of finite-valuation approximable domains is contained in the class of countably based
FS-domains and contains all countably based bc-domains, while it is incomparable with the class
of RB-domains.
    The paper is organized as follows. Sections 2– 5 prove the finite-poset results. The remaining
sections define ωFVA, prove the saturation theorem, construct the randomized finite kernels,
establish the kernel-lifting and generator-transfer principles, and prove theorem 10.4.

2. Preliminaries
     We recall the domain-theoretic notions used below and then fix the finite-dimensional nota-
tion for valuations. For general background on domains and continuous valuations, see [1, 4].
Throughout, N = {0, 1, 2, . . .}, and directed sets are understood to be nonempty.
     A subset E of a poset is directed if every two elements of E have an upper bound in E. A dcpo
is a poset in which every directed subset has a supremum. A dcpo is pointed if it has a least element,
usually denoted by ⊥. Let P be a dcpo. A subset U ⊆ P is called Scott open, if U is upper, i.e.
U =↑ U = {x ∈ P : ∃a ∈ U, a ≤ x}, and sup D ∈ U implies U ∩ D , ∅ for any directed D ⊆ P. all
Scott open subsets of P forms a topology, which is called the Scott topology of P.
     For elements a, b of a dcpo, we write a ≪ b and say that a is way below b if, whenever
b ≤ sup E for a directed set E, there is e ∈ E with a ≤ e. A dcpo D is continuous if, for every x ∈ D,
the set {a ∈ D : a ≪ x} is directed and has supremum x. A domain is a continuous dcpo. A subset
B ⊆ D is a basis if Bx = {b ∈ B : b ≪ x} is directed with supremum x for every x ∈ D. The domain
is countably based if it has a countable basis. A map between dcpos is Scott-continuous if and only
if it is monotone and preserves directed suprema, i.e., it is continuous for the Scott topologies. For
dcpos D and E, we write [D → E] for the dcpo of Scott-continuous maps from D to E, ordered
pointwise:
                             f ≤ g ⇐⇒ f (x) ≤ g(x) for every x ∈ D.



                                                  3


---

Directed suprema in [D → E] are computed pointwise. Thus, for a directed family ( fi ),
                                         !
                                   sup fi (x) = sup fi (x).
                                          i                i
This observation will be used repeatedly when a construction on valuations is lifted pointwise to a
function space. We write DCPO for the category of dcpos and Scott-continuous maps.
Definition 2.1. We use the standard unpointed formulation of FS-domains [4, Definition II-2.15].
Let D be a domain, not necessarily pointed. A Scott-continuous map f : D → D is finitely
separated from the identity if there is a finite set M ⊆ D such that, for every x ∈ D, some m ∈ M
satisfies f (x) ≤ m ≤ x. The set M is called a finite separator for f .
    A family ( fi )i∈I of Scott-continuous self-maps, directed in the pointwise order, is an FS approxi-
mate identity if every fi is finitely separated from the identity and supi fi = idD pointwise. A domain
admitting an FS approximate identity is called an FS-domain. We write FS for the full subcategory
of DCPO consisting of FS-domains.
   For a real number r, write r+ = max{r, 0}.
   Let D be a dcpo and let O(D) be its lattice of Scott-open sets. A continuous valuation on D is a
Scott-continuous map ν : O(D) → [0, ∞] satisfying
                        ν(∅) = 0,       ν(U) + ν(V) = ν(U ∪ V) + ν(U ∩ V).
Thus ν(U) is interpreted as the mass assigned to the observable event U, and the displayed
modularity equation is the finite-additivity law in its form appropriate to open sets. Scott continuity
of ν means that the mass of a directed union of Scott-open sets is the supremum of their masses. It
is a subprobability valuation if ν(D) ≤ 1, and a probability valuation if ν(D) = 1. These valuations
are ordered pointwise and form dcpos denoted by V≤1 (D) and V1 (D). For a Scott-continuous map
 f : D → E,
                                         V≤1 ( f )(ν)(U) = ν( f −1 (U)).
The unit is ηD (x) = δ x , where δ x is the Dirac valuation concentrated at x. We use the same symbol
ηD for its corestriction to V1 (D) when the codomain is clear. A Scott-continuous map
                                              k : D → V≤1 (E)
is called a valuation kernel; for each input x, the valuation k(x) describes a probabilistic output in
E. Its Kleisli extension is                      Z
                                    (k† ν)(U) =         k(x)(U) dν(x).                              (1)
                                                    D
Formula (1) averages the output valuation k(x) against the input valuation ν. The correspond-
ing multiplication, which takes the barycentre of a valuation of valuations, is denoted by µD :
V≤1 (V≤1 (D)) → V≤1 (D). The same formulas restrict to V1 . We use without further mention the
canonical Scott-continuous inclusion V1 (D) ,→ V≤1 (D). Indeed, if f : D → E and ν ∈ V1 (D),
then
                             V1 ( f )(ν)(E) = ν( f −1 (E)) = ν(D) = 1.
Moreover, if k : D → V1 (E) and ν ∈ V1 (D), then
                                       Z                     Z
                          (k ν)(E) =
                            †
                                          k(x)(E) dν(x) =       1 dν = 1.
                                          D                       D
                                                    4


---

   Let P be a finite poset. A subset U ⊆ P is an upper set if x ∈ U and x ≤ y imply y ∈ U. We use
                  ↑x = {y ∈ P : x ≤ y},              ↓A = {x ∈ P : x ≤ a for some a ∈ A}.
Every directed subset of a finite poset has a greatest element, so the Scott-open subsets of P are
exactly its upper sets.
   For finite P, Scott continuity on O(P) is automatic for every monotone map. For x ∈ P, the
Dirac valuation is δ x (U) = 1 if x ∈ U, and δ x (U) = 0 otherwise.
   On a finite poset every subprobability valuation is simple. More precisely, there are unique
                          P
coefficients p x ≥ 0 with x p x ≤ 1 such that
                                  X
                             ν=       px δx ,     p x = ν(↑x) − ν(↑x \ {x}).                   (2)
                                 x∈P
This is the standard finite-space description of the valuation powerdomain; see [9, Section 4.5]. We
therefore identify V≤1 (P) with the Euclidean simplex
                                                                   
                                                        X          
                                  ∆≤1 (P) =                          .
                                                   P
                                                                    
                                              p ∈      :     p   ≤ 1
                                                                   
                                                 R ≥0         x    
                                                                    
                                                                   
                                                         x∈P
For A ⊆ P, write p(A) = x∈A p x . The stochastic order on valuations is
                           P

                    p ≤st q   ⇐⇒         p(U) ≤ q(U)                for every upper set U ⊆ P.     (3)
Thus q is above p when every upward-closed observation receives at least as much mass under q as
under p. On a finite poset this order permits both adding mass and moving existing mass upward; it
is generally different from the coordinatewise order on the atomic coefficients. The positive support
of p is
                                     supp(p) = {x ∈ P : p x > 0}.
The standard characterizations of stochastic order on partially ordered spaces [14] give the following
finite form. The subprobability version is obtained from the probability version by adjoining a fresh
least point and placing the missing mass there.
Lemma 2.2. For p, q ∈ V≤1 (P), the following conditions are equivalent:
  (i) p ≤st q;
 (ii) for every nonnegative monotone map g : P → R,
                                       X             X
                                          p x g(x) ≤   q x g(x).
                                               x∈P                      x∈P

Proof. The implication (ii)⇒(i) follows by taking g = 1U for every upper set U. Conversely, let
0 < t1 < · · · < tm be the distinct positive values of a nonnegative monotone map g : P → R, and put
                                       U j = {x ∈ P : g(x) ≥ t j }.
Each U j is an upper set. With t0 = 0,
                                                 m
                                                 X
                                          g=               (t j − t j−1 )1U j .
                                                     j=1

If p ≤st q, applying the upper-set inequalities to this nonnegative linear combination gives
                                      X              X
                                          p x g(x) ≤     q x g(x).
                                         x∈P                      x∈P
                                                              5


---

    A finite poset is a continuous dcpo with a finite basis. Jones’s results therefore imply that
V≤1 (P) is a countably based domain; a countable basis is obtained from simple valuations with
rational coefficients [9, Corollaries 5.4 and 5.5].
    Directed suprema in the valuation powerdomain are computed pointwise on Scott-open sets [9,
10]. Thus, if D ⊆ ∆≤1 (P) is directed and p = sup D, then
                         p(U) = sup q(U)         for every upper set U ⊆ P.                       (4)
                                  q∈D


3. Construction of the approximating maps
    This section constructs the basic approximation used throughout the paper. For a valuation p on
a finite poset, we repeatedly remove mass from the maximal elements of its positive support. The
resulting one-parameter family (Φt )t≥0 moves every valuation downward and converges back to it
as t → 0. The main issue, addressed in the next section, is to choose the scale so that the maps also
preserve the stochastic order.
    Throughout this section, P is nonempty. Put
                                  n = |P|,       KP = n(n + 1)n−1 .
For p ∈ ∆≤1 (P) with p , 0, put
                                        A(p) = Max(supp(p))
to be the set of maximal elements of supp(p), which we also called the frontier. A subset of a poset
is an antichain if no two distinct elements are comparable. Thus A(p) is a nonempty antichain. For
every nonempty antichain A ⊆ P, define
                                         c(A) = (n + 1) n−|↓A| .                                  (5)
The exact formula is chosen to enforce the comparison in lemma 3.1: if one frontier lies strictly
below another, then the lower frontier is eroded at a substantially larger rate. This separation of
rates is what later prevents two ordered trajectories from crossing.
Lemma 3.1. Let A and B be nonempty antichains of P. If A ⊆ ↓B and A , B, then
                                    c(A) ≥ (n + 1)c(B) > nc(B).
Proof. For every antichain E, the maximal elements of ↓E are exactly the points of E. Hence
A ⊆ ↓B implies ↓A ⊆ ↓B. Equality of these two lower sets would imply A = B, so the inclusion is
strict. Therefore |↓A| ≤ |↓B| − 1, and (5) gives
                                    c(A)
                                         = (n + 1)|↓B|−|↓A| ≥ n + 1.
                                    c(B)


   Fix p ∈ ∆≤1 (P). We define
                                        ϕ p : [0, ∞) −→ ∆≤1 (P)


                                                   6


---

recursively. During one stage, all coordinates on the current frontier are decreased at the common
rate c(A), while all other coordinates are kept fixed. The stage ends when the first frontier coordinate
reaches zero; the frontier is then recomputed from the smaller support.
    Set q0 = p and s0 = 0. Suppose that q j and s j have been defined. If q j = 0, define ϕ p (s) = 0 for
all s ≥ s j and terminate the recursion. If q j , 0, set
                                                                                 (q j )a
                            A j = A(q j ),        c j = c(A j ),   τ j = min             .
                                                                            a∈A j c j

The set A j is finite and nonempty, and (q j )a > 0 for every a ∈ A j , hence τ j > 0. For 0 ≤ u ≤ τ j ,
define                                                             X
                                        ϕ p (s j + u) = q j − uc j     δa .                           (6)
                                                                  a∈A j
Equivalently,                                        
                                                     (q j ) x − uc j , x ∈ A j ,
                                                     
                                   ϕ p (s j + u) x = 
                                                    
                                                     (q j ) x ,
                                                                       x < A j.
The definition of τ j implies that every coordinate remains nonnegative. The total mass does not
increase, so ϕ p (s j + u) ∈ ∆≤1 (P) for 0 ≤ u ≤ τ j . Define
                                 s j+1 = s j + τ j ,       q j+1 = ϕ p (s j+1 ).
At least one coordinate indexed by A j is zero in q j+1 . Coordinates outside A j are unchanged, while
the remaining coordinates indexed by A j stay nonnegative. Consequently,
                                         supp(q j+1 ) ⊊ supp(q j ).
Thus the recursion has at most | supp(p)| ≤ n nonzero steps and eventually reaches the zero vector.
   Formula (6) shows that ϕ p is continuous on each interval [s j , s j+1 ]. At the common endpoint of
two consecutive intervals, both definitions have value q j+1 . If qm = 0, the extension ϕ p (s) = 0 for
s ≥ sm also agrees at sm . Hence ϕ p is continuous on [0, ∞). For t ≥ 0, define
                             Φt : ∆≤1 (P) −→ ∆≤1 (P),             Φt (p) = ϕ p (t).
Lemma 3.2. For every p ∈ ∆≤1 (P) and s, t ≥ 0, the following hold.
   (i) Φt (p) ≤ p coordinatewise, and hence Φt (p) ≤st p;
  (ii) Φ0 = id and Φ s+t = Φ s ◦ Φt ;
 (iii) if s ≥ t, then Φ s (p) ≤ Φt (p) coordinatewise.
Proof. On each stage interval [s j , s j+1 ], we have
                                                     X
                          ϕ p (s j + u) = q j − uc j   δa              (0 ≤ u ≤ τ j ).
                                                       a∈A j

Hence, for every x ∈ P,
                                                  (q j ) x − uc j ,      x ∈ A j,
                                                  
                                                  
                                ϕ p (s j + u) x = 
                                                 
                                                  (q j ) x ,
                                                  
                                                                x < A j.
Thus no coordinate increases during a stage. Since the endpoint of one stage is the initial state of
the next, it follows inductively that ϕ p (t) ≤ p coordinatewise for every t ≥ 0. Therefore
                                            Φt (p) = ϕ p (t) ≤ p
                                                       7


---

coordinatewise. Hence Φt (p) ≤st p. This proves (i).
    The equality Φ0 = id follows from ϕ p (0) = p. We prove the semigroup identity. Fix t ≥ 0 and
put
                                       r = Φt (p) = ϕ p (t).
Here ϕr denotes the map obtained from the same recursion with initial value r. We claim that
                                     ϕr (u) = ϕ p (t + u)           (u ≥ 0).                           (7)
If r = 0, both sides are zero. Assume that r , 0. Since r = ϕ p (t), there is a unique j such that
s j ≤ t < s j+1 . Write t = s j + v, where 0 ≤ v < τ j . Then
                                                            X
                                             r = q j − vc j   δa .
                                                            a∈A j

No coordinate has become zero between s j and t, so supp(r) = supp(q j ) and A(r) = A j . The
coefficient in the first recursive step starting from r is therefore c j , and the length of that step is
                                                                !
                                         ra          (q j )a
                                   min = min                 − v = τ j − v.
                                   a∈A j c j   a∈A j  cj
Hence, for 0 ≤ u ≤ τ j − v,
                                         X                         X
                       ϕr (u) = r − uc j     δa = q j − (v + u)c j     δa = ϕ p (t + u).
                                       a∈A j                          a∈A j

At u = τ j − v, both sides equal q j+1 . If q j+1 = 0, both maps remain zero. If q j+1 , 0, both recursions
compute the same set A(q j+1 ), the same coefficient c(A(q j+1 )), and the same number
                                                             (q j+1 )a
                                                 min                    .
                                               a∈A(q j+1 ) c(A(q j+1 ))

They therefore agree on the next recursive interval and again have the same endpoint. Repeating
this argument over the finitely many remaining intervals proves (7). Consequently,
                               Φ s (Φt (p)) = ϕr (s) = ϕ p (t + s) = Φ s+t (p),
which proves (ii).
   If s ≥ t, write s = t + u with u ≥ 0. By (ii) and then (i),
                                      Φ s (p) = Φu (Φt (p)) ≤ Φt (p)
coordinatewise. This proves (iii).
   The construction above gives a decreasing semigroup below the identity, but it does not yet
show that each Φt is monotone for the stochastic order. Since that order is determined by upper-set
masses, the next section studies the evolution of Φt (p)(U) for each upper set U.

4. Upper-set inequalities and order preservation
     The purpose of this section is twofold. First, we obtain uniform upper and lower bounds on
the rate at which an upper-set mass decreases. Second, we use those local rate comparisons in a
first-contact argument to prove that two initially ordered trajectories cannot cross. This will yield
the order preservation needed for Scott continuity and finite separation.
                                                      8


---

Lemma 4.1. Let p ∈ ∆≤1 (P) and let U ⊆ P be an upper set. If p(U) > 0, then A(p) ∩ U , ∅.
Proof. Choose x ∈ supp(p) ∩ U. Since supp(p) is finite, there is a maximal element a of supp(p)
with x ≤ a. Then a ∈ A(p). Since U is an upper set, a ∈ U.
    For an upper set U ⊆ P and p ∈ ∆≤1 (P), define
                                      
                                      c(A(p)) |A(p) ∩ U|,
                                                                         p , 0,
                             γU (p) = 
                                      
                                                                                                          (8)
                                      0,
                                                                         p = 0.
Lemma 4.2. Let p ∈ ∆≤1 (P), let U be an upper set, and let s ≥ 0. There is η > 0 such that
                        Φ s+h (p)(U) = Φ s (p)(U) − hγU (Φ s (p))           (0 ≤ h ≤ η).                  (9)
Proof. Put q = Φ s (p). If q = 0, then Φ s+h (p) = 0 for all h ≥ 0, and (9) holds for every η > 0.
Suppose that q , 0. By Lemma 3.2(ii), Φ s+h (p) = Φh (q). Choose
                                                     qa
                                        η = min            > 0.
                                            a∈A(q) c(A(q))

For 0 ≤ h ≤ η, the first recursive formula for the initial value q gives
                                                            X
                                    Φh (q) = q − h c(A(q))       δa .
                                                                a∈A(q)

Evaluation on U gives (9).
Lemma 4.3. For every upper set U ⊆ P, every p ∈ ∆≤1 (P), and every t ≥ 0,
                                             +
                       Φt (p)(U) ≤ p(U) − t = max{p(U) − t, 0}.                                          (10)
Proof. Put h(s) = Φ s (p)(U). If h(t) = 0, then (10) is immediate. Suppose that h(t) > 0. By
Lemma 3.2(iii), h(s) ≥ h(t) > 0 for 0 ≤ s ≤ t.
    Insert into [0, t] all numbers s j from the recursion for p that lie in (0, t). This gives a finite
partition
                                         0 = r0 < r1 < · · · < rm = t
such that each interval [ri−1 , ri ] is contained in one of the intervals [s j , s j+1 ]. Let Ai be the corre-
sponding set A j . By (6),
                                h(ri ) = h(ri−1 ) − (ri − ri−1 )c(Ai )|Ai ∩ U|.
Since h(ri−1 ) > 0, Lemma 4.1 gives Ai ∩ U , ∅. Also c(Ai ) ≥ 1 by (5). Hence
                                        h(ri−1 ) − h(ri ) ≥ ri − ri−1 .
Summing over i yields
                                                                 m
                                                                 X
                          p(U) − Φt (p)(U) = h(0) − h(t) ≥              (ri − ri−1 ) = t.
                                                                  i=1
Thus Φt (p)(U) ≤ p(U) − t, which proves (10) when h(t) > 0.
Lemma 4.4. For every nonempty upper set U ⊆ P, every p ∈ ∆≤1 (P), and every t ≥ 0,
                                                       +
                               Φt (p)(U) ≥ p(U) − KP t .                                                 (11)
                                                      9


---

Proof. On a recursive interval with active antichain A, the function s 7→ Φ s (p)(U) has derivative
                                           −c(A)|A ∩ U|.
Since A , ∅ implies |↓A| ≥ 1,
                             c(A) ≤ (n + 1)n−1 ,        c(A)|A ∩ U| ≤ KP .
Partition [0, t] by the finitely many recursive endpoints; if the recursion reaches zero before t,
include the remaining interval, on which the derivative is zero. Summation over the resulting
intervals gives
                                      p(U) − Φt (p)(U) ≤ KP t.
Thus Φt (p)(U) ≥ p(U) − KP t. Since Φt (p)(U) ≥ 0, (11) follows.
Corollary 4.5. For every nonempty upper set U ⊆ P,
                           +                      +
                p(U) − KP t ≤ Φt (p)(U) ≤ p(U) − t                (p ∈ V≤1 (P), t ≥ 0).          (12)
Lemma 4.6. If p ≤st q and p , 0, then A(p) ⊆ ↓A(q).
Proof. Let a ∈ A(p). Since pa > 0, we have p(↑a) > 0, and therefore q(↑a) > 0. Choose
x ∈ supp(q) ∩ ↑a. Since supp(q) is finite, there is a maximal element b of supp(q) with x ≤ b. Then
b ∈ A(q) and a ≤ x ≤ b.
Lemma 4.7. Let p ≤st q, and let U be an upper set such that p(U) = q(U). Then γU (p) ≥ γU (q).
Proof. If p(U) = q(U) = 0, then neither support meets U, and hence γU (p) ≥ γU (q) = 0. Suppose
that p(U) = q(U) > 0. By Lemma 4.1, both A(p) ∩ U and A(q) ∩ U are nonempty. Lemma 4.6
gives A(p) ⊆ ↓A(q).
    If A(p) = A(q), then the two values of γU are equal. If A(p) , A(q), Lemma 3.1 gives
c(A(p)) > nc(A(q)), and hence
                    γU (p) ≥ c(A(p)) > nc(A(q)) ≥ |A(q) ∩ U|c(A(q)) = γU (q).


Theorem 4.8. For every t ≥ 0, the map Φt is order preserving, i.e., p ≤st q =⇒ Φt (p) ≤st Φt (q).
Proof. Fix p ≤st q. For every upper set U ⊆ P, define
                            dU (s) = Φ s (q)(U) − Φ s (p)(U)      (s ≥ 0).
Each dU is continuous and dU (0) ≥ 0. Suppose, for a contradiction, that some dU takes a negative
value. Let
                          σ = inf{s ≥ 0 : dU (s) < 0 for some upper set U}.
Continuity gives
                                 dU (σ) ≥ 0     for every upper set U.
In particular, Φσ (p) ≤st Φσ (q). Apply Lemma 4.2 to both maps s 7→ Φ s (p) and s 7→ Φ s (q) at s = σ.
Since there are only finitely many upper sets, there is η > 0 such that, for every upper set U and
0 ≤ h ≤ η,
                          dU (σ + h) = dU (σ) + h γU (Φσ (p)) − γU (Φσ (q)) .
                                                                           

                                                   10


---

If dU (σ) = 0, Lemma 4.7 shows that the coefficient of h in this formula is nonnegative. Hence
dU (σ + h) ≥ 0 for 0 ≤ h ≤ η. For every upper set with dU (σ) > 0, continuity gives a number ηU > 0
such that dU (σ + h) > 0 for 0 ≤ h ≤ ηU . Since the set of upper sets is finite, we may reduce η so
that these inequalities hold simultaneously. It follows that no dU is negative on [σ, σ + η].
     On the other hand, negative values must occur arbitrarily close to the right of σ. Otherwise,
some number larger than σ would still be a lower bound of the set whose infimum defines σ.
This contradiction proves that dU (s) ≥ 0 for every upper set U and every s ≥ 0. Therefore
Φ s (p) ≤st Φ s (q) for all s ≥ 0.

5. Probabilistic powerdomains of finite posets are FS-domains
    The preceding sections constructed an order-preserving semigroup. To turn the small-time maps
Φt into an FS approximate identity, two additional properties are required. Each Φt must preserve
directed suprema, and for t > 0 it must admit a finite separator. The upper-set estimate supplies
both: it compares Φt (p) with a simultaneous finite approximation of p, and it allows every atomic
coordinate to be rounded down to a fixed rational grid.
Proposition 5.1. For every t ≥ 0, the map Φt : ∆≤1 (P) −→ ∆≤1 (P) is Scott-continuous.
Proof. By Theorem 4.8, Φt is order preserving. It remains to prove that it preserves directed
suprema.
    Let D ⊆ ∆≤1 (P) be directed, put p = sup D, and let r = supq∈D Φt (q). The image Φt (D) is
directed because Φt is order preserving. Since q ≤st p for every q ∈ D, order preservation also gives
Φt (q) ≤st Φt (p), and hence
                                               r ≤st Φt (p).                                     (13)
Fix ε > 0. By (4), for every upper set U there is qU ∈ D such that qU (U) > p(U) − ε. There are
only finitely many upper sets. Directedness therefore provides one qε ∈ D above all the finitely
many qU , and hence
                             qε (U) > p(U) − ε        for every upper set U.                     (14)
Lemma 4.3 and (14) imply
                                                             +
                                   Φε (p)(U) ≤ p(U) − ε ≤ qε (U)
for every upper set U. Indeed, the second inequality is immediate when p(U) ≤ ε, and other-
wise it follows from (14). Hence Φε (p) ≤st qε . Applying Φt and using order preservation and
Lemma 3.2(ii), we obtain
                                  Φt+ε (p) = Φt (Φε (p)) ≤st Φt (qε ) ≤st r.                     (15)
For fixed p, the map s 7→ Φ s (p) is continuous. For each upper set U, letting ε → 0 in (15) gives
Φt (p)(U) ≤ r(U). Since the finite family of upper-set coordinates determines the stochastic order,
this ordinary coordinate limit yields Φt (p) ≤st r. Together with (13), this yields
                                       Φt (p) = r = sup Φt (q).
                                                      q∈D

Therefore Φt preserves directed suprema and is Scott-continuous.
Proposition 5.2. For every t > 0, the Scott-continuous map Φt is finitely separated from id∆≤1 (P) .
                                                 11


---

Proof. Choose N ≥ 1 such that n/N < t, and let MN = m ∈ ∆≤1 (P) : Nm x ∈ N for every x ∈ P .
                                                                    
For every m ∈ MN , write m x = k x /N, where k x ∈ N. Since x∈P m x ≤ 1, we have x∈P k x ≤ N.
                                                                      P                P
In
n particular,    o 0 ≤ k x ≤ N for every x ∈ P. Thus each coordinate m x belongs to the finite set
 0, N , . . . , 1 . Since P is finite, only finitely many such vectors exist. Hence MN is finite. For
    1

p ∈ ∆≤1 (P), round each coordinate down by setting
                                                         ⌊N p x ⌋
                                                  λ xp =          .
                                                           N
For every x, λ xp ≤ p x , so                  X          X
                                                  λ xp ≤     p x ≤ 1.
                                          x∈P        x∈P
Thus λ p ∈ MN and λ p ≤ p coordinatewise; in particular, λ p ≤st p. For every upper set U,
                                                        |U|    n
                                  0 ≤ p(U) − λ p (U) ≤      ≤     < t.                           (16)
                                                         N     N
If p(U) ≤ t, Lemma 4.3 gives Φt (p)(U) = 0 ≤ λ p (U). If p(U) > t, then (16) gives p(U) − t < λ p (U),
while Lemma 4.3 gives
                                    Φt (p)(U) ≤ p(U) − t < λ p (U).
Thus Φt (p) ≤st λ p ≤st p for every p, and MN is a finite separator for Φt .
Theorem 5.3. For every finite poset P, the powerdomain V≤1 (P) is a countably based FS-domain.
Proof. If P = ∅, then V≤1 (P) is a singleton. Assume that P is nonempty. By the standard results
recalled in Section 2, V≤1 (P)  ∆≤1 (P) is a countably based domain. It remains to construct an FS
approximate identity.
    For k ∈ N, put tk = 2−k . Since tk+1 < tk , Lemma 3.2(iii) gives, for every p,
                                        Φtk (p) ≤st Φtk+1 (p) ≤st p.                             (17)
Each Φtk is Scott-continuous by Proposition 5.1 and finitely separated by Proposition 5.2.
   Fix p ∈ ∆≤1 (P). The map t 7→ Φt (p) is continuous and Φ0 (p) = p, so for every upper set U,
                                         lim Φtk (p)(U) = p(U).
                                        k→∞
The sequence in (17) is directed. If r denotes its supremum, then (4) gives
                          r(U) = sup Φtk (p)(U) = lim Φtk (p)(U) = p(U)
                                    k                  k→∞

for every upper set U. Hence r = p. Thus supk Φtk = id pointwise, and (Φtk )k∈N is an FS approximate
identity.
   Thus the maps (Φ2−k )k∈N form an explicit increasing FS approximate identity on V≤1 (P). This
completes the subprobability analysis for finite posets and provides the finite generators used in the
second half of the paper.
   Let Q be a finite nonempty poset. Its normalized probability powerdomain is
                                                                     
                                                            X        
                           V1 (Q) = ∆1 (Q) =           Q
                                                                   =    ,
                                                                     
                                                  p ∈      :   p     1
                                                                     
                                                     R ≥0       x    
                                                                      
                                                                     
                                                                x∈Q


                                                    12


---

ordered by the same upper-set inequalities. Recall that a least element is below every point, whereas
a minimal element merely has no strictly smaller point. This distinction is decisive here. If Q
has a least element, that point can store the missing mass and the normalized case reduces to the
subprobability case. If Q has no least element, the probability vectors supported on Min(Q) form
an infinite family of minimal elements of V1 (Q), which is incompatible with a finite separator.
Proposition 5.4. If Q has a least element ⊥, then restriction of coordinates gives an order isomor-
phism
                                     V1 (Q)  V≤1 (Q \ {⊥}).
Consequently, V1 (Q) is a countably based FS-domain.
Proof. This is the finite-poset instance of Edalat’s lifting trick [6, Lemma 6.1]. Put R = Q \ {⊥}.
Restriction sends p ∈ V1 (Q) to p|R ∈ V≤1 (R). Its inverse sends µ ∈ V≤1 (R) to the probability
          µ defined by
valuation b
                               µ x = µ x (x ∈ R),
                               b                       µ⊥ = 1 − µ(R).
                                                       b
An upper set of Q not containing ⊥ is exactly an upper set of R, whereas an upper set containing ⊥
is necessarily Q itself, on which every probability valuation has value 1. Hence restriction and its
inverse preserve and reflect the stochastic order. They are therefore inverse order isomorphisms of
dcpos. The final assertion follows from theorem 5.3; when Q = {⊥}, both sides are singletons.
Proposition 5.5. If Q has no least element, then no self-map f : V1 (Q) → V1 (Q) admits a finite
set F ⊆ V1 (Q) such that, for every p ∈ V1 (Q), some m ∈ F satisfies f (p) ≤st m ≤st p. In particular,
V1 (Q) is not an FS-domain.
Proof. Let M = Min(Q). Since Q is finite, every element lies above a minimal element. Thus, if M
were a singleton, its unique element would be below every point of Q and would be a least element.
Hence |M| ≥ 2.
    Let p ∈ V1 (Q) be supported on M, and suppose that q ≤st p. For every m ∈ M, the set Q \ {m}
is upper, and therefore
                         1 − qm = q(Q \ {m}) ≤ p(Q \ {m}) = 1 − pm .
Thus qm ≥ pm for every m ∈ M. Since m∈M pm = 1 and q also has total mass one, it follows that
                                     P
qm = pm for every m ∈ M and q(Q \ M) = 0. Hence q = p, so every probability valuation supported
on M is a minimal element of V1 (Q). Then
                                 F M = {p ∈ V1 (Q) : supp(p) ⊆ M}
is infinite because |M| ≥ 2.
     If a finite set F separated a self-map f from the identity, then for each p ∈ F M there would be
m p ∈ F with f (p) ≤st m p ≤st p. Minimality of p would give m p = p, forcing the finite set F to
contain the infinite set F M , a contradiction.
Corollary 5.6. For every finite nonempty poset Q,
                     V1 (Q) is an FS-domain        ⇐⇒    Q has a least element.
In the positive case, V1 (Q) is countably based.

                                                   13


---

    The finite-poset analysis is now complete: subprobability valuations always form an FS-domain,
whereas normalized probability valuations do so exactly when the underlying finite poset has a
least element. We now use the subprobability spaces V≤1 (P) as finite-dimensional factorization
objects for a class of general domains.

6. Finite-valuation approximate identities
     The preceding results show that the subprobability valuation domains of finite posets are FS-
domains. We now use these spaces as factorization objects in order to define a full subcategory that
is Cartesian closed and closed under both valuation powerdomains. This will give a solution to the
generalized Jung–Tix problem.
     The basic idea is to consider domains that can be approximated from below through subproba-
bility valuation domains of finite posets.
Definition 6.1. Let D, E be dcpos. A Scott-continuous map a : D → E is finite-valuation factorable
if there are a finite poset P and Scott-continuous maps
                                                    p         e
                                             D→
                                              − V≤1 (P) →
                                                        − E
such that a = e ◦ p. We then say that a factors through V≤1 (P). If D = E and a ≤ idD , then a is
called a finite-valuation approximant of D.
Definition 6.2. Let D be a domain. A finite-valuation approximate identity on D is a sequence of
finite-valuation approximants
                                     an = en pn : D −→ D             (n ∈ N)
such that
                                     an ≤ an+1 ≤ idD ,        sup an = idD                        (18)
                                                              n∈N
pointwise. No equation pn en = idV≤1 (Pn ) is required. Thus the intermediate valuation domain need
not be a retract of D. A domain admitting such an approximate identity is called finite-valuation
approximable. We write ωFVA for the full subcategory of DCPO whose objects are these domains.
                         p              e
    In a factorization D →
                         − V≤1 (P) →− D, the map p may be viewed as a finite probabilistic encoding
and e as a reconstruction map. No retraction equation is imposed, and the approximating self-map
need not have finite image. Thus this is a different finite-structure condition from the finite-image
deflations used for RB-domains.
Remark 6.3. There is a direct finite-poset analogue of definitions 6.1 and 6.2. Recall that a deflation
on a domain D is a Scott-continuous map d : D → D with finite image and d ≤ idD , and that an
RB-domain is a domain admitting a directed approximate identity of deflations.
    For a domain D, the following conditions are equivalent:
  (i) There are finite posets Pn and Scott-continuous maps
                                               pn        en
                                            D −→ Pn −→ D             (n ∈ N)
      such that, with an = en pn ,
                                        an ≤ an+1 ≤ idD ,         sup an = idD
                                                                    n∈N
      pointwise.
                                                        14


---

  (ii) D is a countably based RB-domain.
Thus, replacing the intermediate valuation domains V≤1 (Pn ) in definition 6.2 by the finite posets
Pn gives precisely the countably based RB-domains. No equation pn en = idPn is required. If
sequences are replaced throughout by arbitrary directed families, the same factorization condition
characterizes all RB-domains.
Lemma 6.4. For every finite poset P, one has V≤1 (P) ∈ ωFVA. Moreover, every D ∈ ωFVA has a
least element.
Proof. The constant sequence an = idV≤1 (P) , with pn = en = idV≤1 (P) , is a finite-valuation approx-
imate identity, so V≤1 (P) ∈ ωFVA. Given D ∈ ωFVA, choose a finite-valuation approximant
a = e ◦ p ≤ idD . Since the zero valuation is the least element of V≤1 (P), for every x ∈ D,
e(0) ≤ e(p(x)) = a(x) ≤ x. Thus e(0) is the least element of D.
Lemma 6.5 ([4, Lemma II-2.16]). Let D be a dcpo and let f : D → D be Scott-continuous and
finitely separated from the identity. Then f (x) ≪ x for every x ∈ D.
    The next lemma is the mechanism that flattens two levels of approximation. An outer map
ai may factor through an intermediate object, while that intermediate object has its own inner
approximate identity hi, j . The double family need not be directed, so simply taking a diagonal
sequence is not sufficient. Finite separation allows one to compare the squares h2i, j on finitely many
separator points and thereby obtain a directed family. A subset C of a directed poset S is cofinal if
every s ∈ S is below some c ∈ C.
Lemma 6.6. Let D be a domain and let (ai )i∈N be an increasing sequence of Scott-continuous maps
such that
                               ai ≤ idD ,        sup ai = idD .
                                                            i
For every i, let (hi, j ) j∈N be an increasing sequence of Scott-continuous maps such that
                                      hi, j ≤ idD ,        sup hi, j = ai ,
                                                                j

and assume that every hi, j is finitely separated from the identity. Then
                                            S = {h2i, j : i, j ∈ N}
is directed, has supremum idD , and contains an increasing cofinal sequence. Every member of S is
finitely separated. If hi, j factors through an object B, then h2i, j factors through the same object.
Proof. Let q1 , . . . , qr be maps among the hi, j , and let Ml be a finite separator for ql . By lemma 6.5,
ql (m) ≪ m for every m ∈ Ml . Repeated interpolation gives ql (m) ≪ rl,m ≪ sl,m ≪ tl,m ≪ m. There
are only finitely many pairs (l, m). Since supi ai (m) = m and supi ai (sl,m ) = sl,m , and since (ai )i is
increasing, one index i may be chosen so that
                                    tl,m ≤ ai (m),     rl,m ≤ ai (sl,m )
for all relevant pairs (l, m). Since hi, j = ai , choose one j such that
                                    W

                                  sl,m ≤ hi, j (m),        ql (m) ≤ hi, j (sl,m )


                                                      15


---

for every (l, m). Put H = hi, j . Given x ∈ D, choose m ∈ Ml with ql (x) ≤ m ≤ x. Then
                                 q2l (x) ≤ ql (m) ≤ H(sl,m ) ≤ H 2 (m) ≤ H 2 (x).
Thus q2l ≤ H 2 for every l, and S is directed.
    Fix x ∈ D and y ≪ x. Choose y ≪ r ≪ s ≪ t ≪ x. Choose i with t ≤ ai (x) and r ≤ ai (s), and
then j with s ≤ hi, j (x) and y ≤ hi, j (s). Hence y ≤ h2i, j (x). Taking the supremum over y ≪ x gives
sup S(x) = x.
    If M separates h, then for every x, there exists m ∈ M such that h2 (x) ≤ h(x) ≤ m ≤ x, so M
also separates h2 . If h = ep through B, then h2 = (h ◦ e)p, which still factors through B. Finally,
enumerate the countable directed set S as (sn )n∈N . Put c0 = s0 , and, after choosing cn , choose
cn+1 ∈ S with cn , sn+1 ≤ cn+1 . Then (cn )n is increasing and cofinal in S.
Theorem 6.7. The following statements hold.
  (i) Every D ∈ ωFVA has a finite-valuation approximate identity whose members are finitely
      separated from the identity. Consequently D is an FS-domain.
 (ii) Let D be a domain and suppose that there is an increasing sequence
                                                        _
                                   an = en pn ≤ idD ,      an = idD ,
                   pn      en
       where D −→ Bn −→ D and Bn ∈ ωFVA. Then D ∈ ωFVA, and D has an approximate identity
       as in (i).
Proof. For (i), let ai = ei pi be a finite-valuation approximate identity on D, with intermediate object
V≤1 (Pi ). By theorem 5.3, choose an increasing FS approximate identity (qi, j ) j∈N on V≤1 (Pi ). Put
                                                  hi, j = ei qi, j pi .
For fixed i, the sequence (hi, j ) j is increasing. Directed suprema in function spaces are computed
pointwise, and ei is Scott-continuous; hence, for every x ∈ D,
                                                                               
                    _               _                   _                
                       hi, j  (x) =   e q    p
                                             i i, j i (x) = ei
                                                                
                                                                   q     (p
                                                                      i, j i (x))    = ei pi (x) = ai (x).
                                                                                   
                          j               j                       j
Thus j hi, j = ai . If Mi, j separates qi, j , then ei [Mi, j ] separates hi, j : for x ∈ D, choose m ∈ Mi, j
           W
with qi, j (pi (x)) ≤ m ≤ pi (x) and obtain hi, j (x) ≤ ei (m) ≤ ai (x) ≤ x. Each hi, j factors through the
same space V≤1 (Pi ). Apply lemma 6.6 and take the increasing cofinal sequence supplied there. Its
members remain finitely separated and finite-valuation factorable, and the supremum is idD . This
proves (i).
       For (ii), apply (i) to each Bi and choose an increasing finite-valuation approximate identity
(qi, j ) j on Bi whose members are finitely separated. Put hi, j = ei qi, j pi . If Mi, j ⊆ Bi separates qi, j , then
ei [Mi, j ] separates hi, j : for every x ∈ D, choose m ∈ Mi, j with
                                             qi, j pi (x) ≤ m ≤ pi (x),
and obtain
                                  hi, j (x) ≤ ei (m) ≤ ei pi (x) = ai (x) ≤ x.
Moreover, every hi, j is finite-valuation factorable because qi, j is. As in part (i), Scott continuity of ei
gives j hi, j = ai . Lemma 6.6 therefore produces the required finite-valuation approximate identity
      W
on D.
                                                          16


---

Proposition 6.8. Every object of ωFVA is countably based.
Proof. Let ( fn ) be the finitely separated approximate identity given by theorem 6.7, and let Mn be a
finite separator for fn . Define
                                  B = { f j (m) : j, n ∈ N, m ∈ Mn }.
We use the following elementary basis criterion. If C is a subset of a continuous dcpo such that,
whenever y ≪ x, some c ∈ C satisfies y ≤ c ≪ x, then C is a basis. Indeed, C ∩ {c : c ≪ x} is
cofinal in {y : y ≪ x}. Given c1 , c2 ≪ x, finite interpolation gives c1 , c2 ≪ y ≪ x, and cofinality
supplies c ∈ C with y ≤ c ≪ x; hence the set is directed. Its supremum is x by continuity.
      Let y ≪ x and choose z with y ≪ z ≪ x. Select n with z ≤ fn (x) and then m ∈ Mn with
fn (x) ≤ m ≤ x. Thus y ≪ m. Since j f j (m) = m, choose j with y ≤ f j (m). By lemma 6.5,
                                         W
f j (m) ≪ m. Since m ≤ x, monotonicity of the way-below relation in its second argument gives
f j (m) ≪ x. The criterion applies, and B is a countable basis.
   Recall that D is a Scott-continuous retract of E if there are Scott-continuous maps i : D → E
and r : E → D with r ◦ i = idD .
Corollary 6.9. The category ωFVA is closed under Scott-continuous retracts.
Proof. Let i : D → E and r : E → D satisfy ri = idD . Since a Scott-continuous retract of a domain
is a domain, if (an ) is a finite-valuation approximate identity on E, put bn = r ◦ an ◦ i. Then
                                                                    !
                          bn ≤ bn+1 ≤ idD ,      sup bn = r ◦ sup an ◦ i = idD ,
                                               n              n
and every bn factors through the same finite-poset valuation space as an .

7. Finite monotone-valuation polytopes
    In this section, we study the finite-dimensional function spaces arising at the finite stages of
the approximation. For finite posets A and P, the function space [A → V≤1 (P)] is both a domain-
theoretic function space and a compact convex polytope in a finite-dimensional Euclidean space.
These two descriptions will be used in parallel. The pointwise order provides the order-theoretic
structure needed for monotonicity and approximation from below, whereas the Euclidean realization
permits finite grids, randomized rounding, and reconstruction by finite convex combinations.
    Let A and P be finite posets and put M(A, P) be the set of monotone maps from A to V≤1 (P),
ordered pointwise. Thus an element x ∈ M(A, P) is a monotone map x : A −→ V≤1 (P). For each
a ∈ A, the value x(a) is a subprobability valuation on P. Since every monotone map from a finite
dcpo is Scott-continuous,
                                     M(A, P) = [A → V≤1 (P)].
If A = ∅ or P =n ∅, this is the one-point
                                       o dcpo. Assume that both are nonempty and identify V≤1 (P)
with ∆≤1 (P) = v ∈ R≥0 : p∈P v p ≤ 1 . For x ∈ M(A, P), writing
                       P   P
                                                 X
                                          x(a) =    xa,p δ p ,
                                                   p∈P


                                                   17


---

the whole map x is represented by the vector (xa,p )(a,p)∈A×P ∈ RA×P . Here xa,p is the atomic mass
assigned to p by the valuation x(a).
    A polyhedron in a finite-dimensional real vector space is an intersection of finitely many closed
affine half-spaces, equivalently a set defined by finitely many linear inequalities. A bounded
polyhedron is called a polytope. The set M(A, P) consists exactly of the vectors (xa,p ) satisfying
                                                   X
                                     xa,p ≥ 0,         xa,p ≤ 1,
                                                         p∈P
and                                       X              X
                                                xa,p ≤         xb,p
                                          p∈U            p∈U
whenever a ≤ b in A and U is an upper set of P. The first two families express that every x(a) is
a subprobability valuation, and the last family expresses the monotonicity x(a) ≤st x(b). Since A
and P are finite, only finitely many inequalities occur. They are linear, so the set is convex, and
0 ≤ xa,p ≤ 1, so it is bounded. It is also closed; hence, by the finite-dimensional Heine–Borel
theorem, M(A, P) is a compact convex polytope in RA×P .
    Let Up(P) be the finite family of upper sets of P. For a ∈ A and ∅ , U ∈ Up(P), define the
linear functional
                                                                      X
                      λa,U : M(A, P) −→ R,       λa,U (x) = x(a)(U) =     xa,p .
                                                                            p∈U

The same formula defines a linear functional on the whole ambient space RA×P , and we use the
same symbol for that extension. The coordinate corresponding to the empty upper set is identically
zero and is omitted. The pointwise order on M(A, P) therefore has the equivalent characterization
                     x≤y     ⇐⇒      λa,U (x) ≤ λa,U (y) for all a ∈ A, U ∈ Up(P).
For clarity, write
                                       ΦtP : V≤1 (P) −→ V≤1 (P)
for the map constructed in sections 3 to 5 for the poset P. We lift it pointwise to the finite function
space by
                           Ψt : M(A, P) −→ M(A, P),               Ψt (x) = ΦtP ◦ x;                (19)
equivalently,
                                              Ψt (x)(a) = ΦtP (x(a)).
Since ΦtP is order preserving by theorem 4.8, the composite ΦtP ◦ x is monotone whenever x is
monotone. Thus Ψt is a self-map of M(A, P). Directed suprema in M(A, P) are computed pointwise,
and ΦtP is Scott-continuous by proposition 5.1; hence, for every directed family (xi ) and every
a ∈ A,                                              
                       _             _         _ P                 _
                  Ψt  xi  (a) = Φt  xi (a) =
                                       P
                                                                Φt (xi (a)) =    Ψt (xi )(a).
                        i                 i                i            i
Therefore Ψt is Scott-continuous. If 0 ≤ s ≤ t, then lemma 3.2 gives ΦtP ≤ ΦPs , and consequently
Ψt ≤ Ψ s .
   Finally, for every nonempty upper set U ⊆ P,
                             λa,U (Ψt (x)) = Ψt (x)(a)(U) = ΦtP (x(a))(U).
                                                   18


---

Applying corollary 4.5 to the valuation x(a) yields
                                         +                             +
                          λa,U (x) − KP t ≤ λa,U (Ψt (x)) ≤ λa,U (x) − t .                         (20)
This estimate will convert the Euclidean error of the grid rounding into an order-theoretic error
measured by the flow parameter t.
Lemma 7.1. For all finite posets A, P, the dcpo M(A, P) is an FS-domain.
Proof. Every finite poset is an FS-domain, and V≤1 (P) is an FS-domain by theorem 5.3. Since
every monotone map from the finite dcpo A is Scott-continuous, M(A, P) = [A → V≤1 (P)]. The
claim follows from the Cartesian closedness of FS [4, Proposition II-2.18].
     We next give a finite generating set for the order directions. A convex cone in a real vector space
is a subset closed under addition and multiplication by nonnegative scalars. For a set S of vectors,
its conic hull is                        m                                  
                                         X                                  
                            cone(S ) =       α              α                 .
                                                                            
                                                 s  : m ≥ 0,    ≥ 0, s   ∈ S
                                                                            
                                               i i           i        i     
                                                                             
                                                                            
                                         i=1
A cone C is pointed if C ∩ (−C) = {0}; this condition ensures that x ≤C y defined by y − x ∈ C is
antisymmetric.
    For v = (v p ) p∈P ∈ RP and U ⊆ P, write v(U) = p∈U v p . Define
                                                    P
                               n                                          o
                         C P = v ∈ RP : v(U) ≥ 0 for every upper set U ⊆ P .                 (21)
Thus, for valuations µ, ν on P,
                                    µ ≤st ν       ⇐⇒      ν − µ ∈ CP.
For p ∈ P, the standard basis vector e p ∈ RP has p-coordinate 1 and all other coordinates 0. The
direction e p adds mass at p, while eq − e p moves one unit of mass from p to q. We write p ≺ q
when q covers p, meaning that p < q and there is no r with p < r < q. The cover relations form the
edges of the Hasse graph of P. The dual-cone and Hasse-network description of monotone cones is
classical; see [24].
Lemma 7.2. If p ≺ q denotes a cover relation in P, then
                                                                    
                        C P = cone {e p : p ∈ P} ∪ {eq − e p : p ≺ q} .                            (22)
The cone C P is pointed. Consequently the pointwise order cone of M(A, P) is
                                              Y
                                      C A,P =    C P = C PA ,
                                                   a∈A
and C A,P is pointed.
                                            b = P⊥ . Let
Proof. Adjoin a fresh least element and put P
                                                             
                                        
                                                  X          
                                                              
                                  HPb =                   =    .
                                              P
                                                              
                                         h ∈     :     h     0
                                              b              
                                            R           x    
                                                              
                                        
                                                             
                                                              
                                                     b    x∈P
Deleting the ⊥-coordinate defines a linear isomorphism
                                               T : HPb −→ RP .
                                                     19


---

Its inverse sends v ∈ RP to the vector b
                                       v ∈ HPb defined by
                                                                            X
                                 vp = vp
                                 b             (p ∈ P),           v⊥ = −
                                                                  b                 vp.
                                                                            p∈P

Let
                          bPb = {h ∈ HPb : h(U) ≥ 0 for every upper set U ⊆ P}.
                          C                                                 b
An upper set of Pb not containing ⊥ is exactly an upper set of P, whereas the only upper set
containing ⊥ is P,
                b on which every h ∈ HPb has sum zero. Hence
                                                    bPb) = C P .
                                                 T (C                                                  (23)
      Put
                                  G = cone{ey − e x : x ≺ y in P}
                                                               b ⊆ HPb.
For g ∈ RP ,
            b

                                       ⟨g, ey − e x ⟩ = g(y) − g(x).
                      ∗
Thus the dual cone G consists precisely of the monotone real-valued functions on P:    b it is enough to
                                                                    ∗∗
impose the inequalities on cover relations. We now identify G . Let h ∈ C Pb and let g be monotone.
                                                                              b
         b = 0, subtracting the minimum value of g does not change ⟨g, h⟩. We may therefore
Since h(P)
assume that g ≥ 0. If 0 < t1 < · · · < tm are its distinct positive values and U j = {x : g(x) ≥ t j }, then
each U j is upper and
                                        Xm
                                   g=      (t j − t j−1 )1U j ,  t0 = 0.
                                         j=1
Consequently,
                                                m
                                                X
                                    ⟨g, h⟩ =           (t j − t j−1 )h(U j ) ≥ 0.
                                                 j=1
Conversely, if a vector h has nonnegative pairing with every monotone function, then the constant
                       b = 0, and choosing g = 1U for an upper set U gives h(U) ≥ 0. Hence
functions show that h(P)
                                            G∗∗ = CbPb.
The cone G is finitely generated and therefore closed. The finite-dimensional bipolar theorem now
gives
                                                bPb = G.
                                                C
This is the standard dual-cone description of the Hasse-network cone; see also [24].
    Under T , a cover direction em − e⊥ , with m minimal in P, becomes em , and every other cover
direction becomes eq − e p for a cover p ≺ q in P. Thus C P is generated by em for minimal m and by
the cover roots eq − e p . For an arbitrary p ∈ P, choose a saturated chain
                                      m = x0 ≺ x1 ≺ · · · ≺ xk = p
from a minimal element m. The telescoping identity
                                              k
                                              X
                                   e p = em +   (e xi − e xi−1 )
                                                          i=1

                                                          20


---

shows that every e p lies in this cone, proving (22).
   To prove pointedness, let v ∈ C P ∩ (−C P ). Then v(U) = 0 for every upper set U. Starting with
maximal elements and proceeding downward, the equality
                                                          X
                                        0 = v(↑p) = v p +   vq
                                                            q>p

shows inductively that every coordinate v p is zero. Thus C P is pointed.
   Finally, the order on M(A, P) is pointwise. Hence
              x≤y      ⇐⇒      y(a) − x(a) ∈ C P for every a ∈ A        ⇐⇒   y − x ∈ C PA .
Therefore C A,P = C PA , and a finite product of pointed cones is pointed.
     The next lemma connects the Euclidean constructions below with domain theory. The ran-
domized coefficients will first be shown continuous in the ordinary Euclidean topology. On the
finite-dimensional ordered polytopes at hand, monotonicity then upgrades Euclidean continuity to
Scott continuity.
Lemma 7.3. Let K and L be finite products of polytopes of the form M(A, P) and finite valuation
spaces V≤1 (Q) or V1 (Q). Every monotone Euclidean-continuous map F : K → L is Scott-
continuous.
Proof. Let (xi )i∈I be a directed family in K with supremum x. Consider first one component M(A, P).
Directed suprema are computed pointwise on upper sets, so for every a ∈ A and every p ∈ P,
                  xi (a)(↑p) −→ x(a)(↑p),         xi (a)(↑p \ {p}) −→ x(a)(↑p \ {p}).
The atomic coordinates satisfy
                                 xi (a) p = xi (a)(↑p) − xi (a)(↑p \ {p}).
Hence every atomic coordinate of xi converges to the corresponding coordinate of x. Since there
are only finitely many coordinates, xi → x in the Euclidean topology. The same argument applies
to V≤1 (Q) and V1 (Q), and then componentwise to finite products.
    Euclidean continuity gives F(xi ) → F(x). Since F is monotone, the family (F(xi ))i∈I is directed.
Let y = supi F(xi ). For each upper-set coordinate of L, directed-supremum computation and
Euclidean convergence give
                                  y(U) = sup F(xi )(U) = F(x)(U).
                                             i
These finitely many coordinates determine the order and the underlying valuation, so y = F(x).
Thus F preserves directed suprema and is Scott-continuous.
    The later rounding construction will need a point uniformly separated from the boundary. The
Euclidean interior int K consists of those points that contain a sufficiently small Euclidean ball
inside K.
Lemma 7.4. If A and P are nonempty, then the compact convex polytope M(A, P) has nonempty
Euclidean interior.


                                                   21


---

                                                 n                  o
Proof. The subprobability simplex ∆≤1 (P) = ν ∈ R≥0     P
                                                          : ν(P) ≤ 1 has nonempty interior. Choose
ρ ∈ int ∆≤1 (P), so that every atomic coordinate of ρ is positive and ρ(P) < 1.
    Since A is finite, there exists a strictly order-preserving map c : A −→ (0, 1). Define u(a) =
c(a)ρ. Thus the image of u lies on the open line segment {tρ : 0 < t < 1} ⊆ int ∆≤1 (P). In particular,
every atomic coordinate of every u(a) is positive and u(a)(P) < 1.
    Moreover, if a < b in A and U ⊆ P is a nonempty upper set, then ρ(U) > 0 and hence
u(a)(U) = c(a)ρ(U) < c(b)ρ(U) = u(b)(U). Therefore u satisfies strictly every nontrivial linear
inequality defining M(A, P). Hence u lies in the Euclidean interior of M(A, P).
   We have therefore represented M(A, P) as a compact ordered polytope with a finitely generated
pointed order cone and a nonempty interior.

8. Monotone randomized grid rounding
     The aim of this section is to replace each point of K = M(A, P) by a probability distribution on
finitely many nearby grid points. A deterministic floor map is discontinuous at grid boundaries and
need not preserve the cone order. Therefore, we introduce the random translation to remove the
discontinuity after taking probabilities, while additional translations along the cover-root directions
yield an explicit monotone coupling.
     Fix nonempty finite posets A, P and put K = M(A, P) ⊆ Rd , where d = |A||P|. Coordinates of
RA×P are indexed by pairs (a, p). Let ea,p be the standard basis vector with value 1 in coordinate
(a, p) and 0 elsewhere, and enumerate all these vectors as e1 , . . . , ed . Enumerate the cover-root
directions ea,q − ea,p (a ∈ A, p ≺ q) as ξ1 , . . . , ξr . By lemma 7.2, C A,P = C PA . For each a ∈ A, the
copy of C P in the a-th component is generated by ea,p (p ∈ P) and ea,q − ea,p (p ≺ q). Consequently,
                                                                                        
                  C A,P = cone {ea,p : a ∈ A, p ∈ P} ∪ {ea,q − ea,p : a ∈ A, p ≺ q} .
After enumerating these two finite families as e1 , . . . , ed and ξ1 , . . . , ξr , respectively, the vectors ei
and ξ j generate C A,P .
    For a vector v, write
                                      [0, v] = {tv : 0 ≤ t ≤ 1}
for the line segment from 0 to v. For subsets B1 , . . . , Bm of a vector space, their Minkowski sum is
                                 B1 + · · · + Bm = {b1 + · · · + bm : bi ∈ Bi }.
Define the bounded set
                                            d
                                            X                   r
                                                                X
                                   ZA,P =         [0, 2ei ] +         [0, ξ j ] ⊆ C A,P .                   (24)
                                            i=1                 j=1
This finite Minkowski sum of line segments is called a zonotope. Its role is to contain every possible
rounding error as we shall see; the inclusion in C A,P will ensure that every rounded grid point lies
below the input in the cone order.
    Let U1 , . . . , Ud , S 1 , . . . , S r be independent random variables, each uniformly distributed on
[0, 1), and write U = (U1 , . . . , Ud ). For a real vector w, ⌊w⌋ denotes coordinatewise floor. For


                                                          22


---

z ∈ Rd , define                                                     
                                                      r
                                                         X               
                                         Qz = z − U −
                                                    
                                                          S j ξ j  ∈ Zd .                     (25)
                                                                   j=1
    Let πz be its probability distribution, that is,
                                      πz ({ℓ}) = P(Qz = ℓ)                   (ℓ ∈ Zd ).
When the random inputs need to be displayed explicitly, we write Qz (U, S ) for the same random
vector. In one dimension and without the S j terms, ⌊z − U⌋ equals ⌊z⌋ with probability equal to the
fractional part of z and equals ⌊z⌋ − 1 otherwise. Thus the individual floor map is discontinuous, but
the two probabilities vary continuously with z.
Lemma 8.1. For every z ∈ Rd , πz has finite support. Moreover,
   (i) if πz ({ℓ}) > 0, then
                                                 z − ℓ ∈ ZA,P ;                                  (26)
  (ii) for every ℓ ∈ Z , the function z 7−→ πz ({ℓ}) is continuous.
                         d


Proof. On the event Qz = ℓ, put
                                                       X
                                      θ =z−U −                 S j ξ j − ℓ ∈ [0, 1)d .
                                                           j
Then                                                               X
                                       z−ℓ =U +θ+                        S j ξ j ∈ ZA,P ,
                                                                     j
which proves (i). It also shows that
                                          supp(πz ) ⊆ (z − ZA,P ) ∩ Zd ,
and the set on the right is finite.
   For (ii), let zn → z in Rd and fix ℓ ∈ Zd . On Ω = [0, 1)d+r , write
                                                                        
                                                          r
                                                             X               
                                    qw (u, s) = w − u −   s j ξ j  .
                                                                           j=1
Then                                                           Z
                                             πw ({ℓ}) =             1{qw =ℓ} dω.
                                                               Ω
Since qw (u, s) = ℓ if and only if
                                              r
                                              X
                             ℓi ≤ wi − ui −          s j (ξ j )i < ℓi + 1            (1 ≤ i ≤ d),
                                               j=1
the map w 7−→ 1{qw (u,s)=ℓ} is locally constant at w = z unless, for some coordinate i,
                                                r
                                                X
                                     zi − u i −   s j (ξ j )i ∈ {ℓi , ℓi + 1}.
                                                     j=1
    Let                                                                               
                                                        r
                                                         X                             
                              Bi =                                          , ℓ  +      ,
                                                                                      
                                    (u, s) : z   − u   −   s   (ξ   )  ∈ {ℓ         1}
                                                                                      
                                              i     i       j    j  i     i    i      
                                                                                       
                                                                                      
                                                               j=1
                                                               23


---

and put B =    i=1 Bi . We claim that B has Lebesgue measure zero. Indeed, write
              Sd

                                             Bi = Bi,0 ∪ Bi,1 ,
where, for ε ∈ {0, 1},                                                      
                                                         r
                                                          X                  
                            Bi,ε =                                 = ℓ  + ε   .
                                                                            
                                     (u, s) : z   − u   −   s  (ξ )
                                                                            
                                               i     i       j j i    i     
                                                                             
                                                                            
                                                           j=1
After all variables except ui have been fixed, the defining equality for Bi,ε determines ui uniquely,
namely
                                                       Xr
                                    ui = zi − ℓi − ε −    s j (ξ j )i .
                                                             j=1
Thus every ui -section of Bi,ε contains at most one point and hence has one-dimensional Lebesgue
measure zero. By Fubini’s theorem, the Lebesgue measure of Bi,ε is Ld+r (Bi,ε ) = 0. Consequently,
Ld+r (Bi ) = 0, and, since there are only finitely many coordinates,
                                                  Xd
                                        d+r
                                      L (B) ≤        Ld+r (Bi ) = 0.
                                                  i=1
    It follows that, for almost every (u, s), no coordinate lies on one of the boundary hyperplanes.
Hence there exists a neighborhood N of z such that
                               1{qw (u,s)=ℓ} = 1{qz (u,s)=ℓ}     for all w ∈ N.
Therefore
                                          1{qzn (u,s)=ℓ} −→ 1{qz (u,s)=ℓ}
for almost every (u, s) whenever zn → z. Since these indicator functions are bounded by 1, the
dominated convergence theorem gives
                                             πzn ({ℓ}) −→ πz ({ℓ}).
Thus z 7→ πz ({ℓ}) is continuous.
    Equip Zd with the order induced by C A,P :
                                     ℓ ≤C m ⇐⇒ m − ℓ ∈ C A,P .
Because C A,P is pointed, this is a partial order. A coupling of two probability distributions µ and ν is
a pair of random variables (L, L′ ) defined on the same probability space such that L has distribution
µ and L′ has distribution ν. It is a monotone coupling if L ≤C L′ almost surely, meaning with
probability one. Such a coupling implies that µ is stochastically below ν. The next proposition
constructs such a coupling explicitly for the rounding distributions. Here stochastic order is taken
with respect to the cone-induced order ≤C on Zd by comparison on all upper sets of the underlying
ordered space.
Proposition 8.2. If z, z′ ∈ Rd satisfy z′ − z ∈ C A,P , then πz is stochastically below πz′ for the order
≤C . More precisely, there is a coupling (L, L′ ) of πz and πz′ such that L ≤C L′ almost surely.
Proof. Choose coefficients αi , β j ≥ 0 such that
                                              Xd          r
                                                          X
                                     z −z=
                                      ′
                                                  αi ei +   β jξ j.
                                                i=1              j=1
                                                      24


---

Write β j = n j + θ j , n j ∈ N, 0 ≤ θ j < 1. Using the random variables from equation (25), define
S ′j = (S j + θ j ) mod 1 and δ j = 1{S j +θ j ≥1} . Thus S j + θ j = S ′j + δ j . Translation modulo 1 preserves the
uniform distribution on [0, 1). Hence S 1′ , . . . , S r′ are again independent and uniformly distributed
on [0, 1), and they remain independent of U. Set
                                       L = Qz (U, S ),                     L′ = Qz′ (U, S ′ ),
and put
                                                 r
                                                 X                               r
                                                                                 X
                                w=z−U −                    S jξ j,            m=   (n j + δ j )ξ j .
                                                     j=1                              j=1
Since each ξ j is an integral vector,
                                                       m ∈ C A,P ∩ Zd .
Moreover,
                   r
                   X                           r
                                               X                  d
                                                                  X                  r
                                                                                     X                                 d
                                                                                                                       X
          ′
        z −U −            S ′j ξ j = z − U −         S jξ j +              αi ei +         (n j + δ j )ξ j = w + m +         αi ei .
                    j=1                        j=1                i=1                j=1                               i=1

Because m is integral, coordinatewise flooring gives
                                           X d
                             L −L=m+
                               ′
                                               ⌊wi + αi ⌋ − ⌊wi ⌋ ei .
                                                                 
                                                            i=1
For every i, ⌊wi + αi ⌋ − ⌊wi ⌋ ∈ N, since αi ≥ 0. Hence L′ − L is a nonnegative linear combination of
the generators ξ j and ei , and therefore L′ − L ∈ C A,P . Thus L ≤C L′ with probability one.
    The random variables L and L′ have distributions πz and πz′ , respectively. Indeed, S ′ has the
same distribution as S . Therefore (L, L′ ) is a monotone coupling of πz and πz′ . Finally, let H ⊆ Zd
be an upper set for ≤C . Since L ≤C L′ almost surely,
                                                L∈H               =⇒          L′ ∈ H
almost surely. Consequently, πz (H) = P(L ∈ H) ≤ P(L′ ∈ H) = πz′ (H). Hence πz ≤st πz′ .
    Recall that K = M(A, P) ⊆ Rd is the compact convex polytope introduced above. The distri-
bution πz is defined on the whole integer grid, but near the boundary of K a rounded point may
lie outside K. We therefore move each input a small distance toward a fixed interior point before
rounding. The grid size is chosen proportional to that inward displacement, so the whole rounding
error remains inside the available interior margin.
    Choose u ∈ int K as in lemma 7.4. With respect to a fixed Euclidean norm, write B(u, r) and
B(u, r) for the open and closed balls of radius r around u. Fix r0 > 0 such that B(u, r0 ) ⊆ int K, and
put
                                      RZ = max{∥z∥ : z ∈ ZA,P }.
Choose c > 0 with cRZ < r0 . For 0 < ε < 1/2, define
                                       Jε (x) = (1 − ε)x + εu,                        hε = cε.
Lemma 8.3. For every x ∈ K and every v ∈ R with ∥v∥ < εr0 , one has Jε (x) + v ∈ int K.
                                                                  d




                                                                      25


---

Proof. Write                                                    v
                                   Jε (x) + v = (1 − ε)x + ε u + .
                                                                 ε
The second point lies in B(u, r0 ) ⊆ int K. A strict convex combination of a point of K and an interior
point belongs to int K; see [17, Theorem 6.1].
   Define
                                      Λε = {ℓ ∈ Zd : hε ℓ ∈ K}.
Since K is compact, the rescaled set h−1
                                      ε K is bounded and contains only finitely many integer points.
Restricting ≤C to Λε therefore gives a finite poset, denoted by Lε . For x ∈ K, put
                                                      X
                               pε (x) = π Jε (x)/hε =   π Jε (x)/hε ({ℓ})δℓ .                  (27)
                                                    ℓ∈Λε

Proposition 8.4. The map pε : M(A, P) −→ V1 (Lε ) ⊆ V≤1 (Lε ) is well defined and Scott-continuous.
If the coefficient of δℓ in pε (x) is nonzero, then
                                             hε ℓ ≤C Jε (x).                                         (28)
Proof. If the coefficient at ℓ is nonzero, then π Jε (x)/hε ({ℓ}) > 0, and equation (26) yeilds a z ∈ ZA,P
such that Jε (x)/hε − ℓ = z. Consequently, Jε (x) − hε ℓ = hε z, which proves equation (28). Moreover,
                                          ∥hε z∥ ≤ cεRZ < εr0 ,
so lemma 8.3 applied to v = −hε z gives hε ℓ ∈ int K. Thus the whole distribution is supported on Lε .
    If x ≤ y, then
                                 Jε (y) − Jε (x) 1 − ε
                                                =      (y − x) ∈ C A,P .
                                        hε          hε
The monotone coupling from proposition 8.2 has both marginals supported on Lε , hence pε (x) ≤st
pε (y). Every coefficient in equation (27) is Euclidean-continuous by lemma 8.1. Since the target is
finite-dimensional, lemma 7.3 gives Scott continuity.
   We have obtained the finite probabilistic encoding
                                       pε : M(A, P) −→ V1 (Lε ).
It is Scott-continuous and order preserving, and every grid point occurring with nonzero probability
lies below the contracted input. The next section adds a reconstruction label to each grid point and
arranges the resulting kernels into an increasing approximation of the Dirac unit.

9. Finite stochastic-kernel approximations and kernel lifting
     The map pε records which finite grid states represent an input x, but it does not yet return points
of K = M(A, P). We therefore assign to each grid state ℓ ∈ Lε a point yε (ℓ) ∈ K, obtained by
first replacing it with a suitable finite approximation and then performing the grid rounding. This
yields two associated approximations: a finitely supported probability kernel κε (x) on K, and its
barycentre dε (x) ∈ K.
     Recall that KP ≥ 1 is the constant associated with the family Ψt , characterized by the estimates
                                            +                              +
                             λa,U (v) − KP t ≤ λa,U (Ψt (v)) ≤ λa,U (v) − t
                                                   26


---

for every v, every a ∈ A, every nonempty upper set U ∈ Up(P), and every t > 0. And recall that
c > 0 was chosen above so that cRZ < r0 , and that the grid size is hε = cε. Put
                      RA,P = max{λa,U (z) : z ∈ ZA,P , a ∈ A, ∅ , U ∈ Up(P)},
and set
                                         C∗ = 1 + 2KP + cRA,P .
The finite number RA,P is a uniform bound on the change of every order coordinate λa,U over the
rounding-error set ZA,P . For ℓ ∈ Lε , define
                                      yε (ℓ) = Ψ2ε (hε ℓ) : Lε −→ K.                         (29)
Equivalently, for every a ∈ A,
                              yε (ℓ)(a) = Φ2ε
                                           P
                                              (hε ℓ)(a) = Φ2ε
                                                           P
                                                              hε ℓ(a) .
                                                                    

Thus the grid point hε ℓ ∈ K is moved farther downward, in the order of K, by applying Ψ2ε . This
additional margin is what makes approximations at successive scales comparable.
Lemma 9.1. The map yε : Lε → K is monotone. If the coefficient of δℓ in pε (x) is nonzero, then,
with
                                      ε
                               αε =     ,       βε = C∗ ε,
                                     KP
for every x ∈ K, one has
                               Ψβε (x) ≤ yε (ℓ) ≤ Ψαε (x).                                  (30)
Proof. Monotonicity follows from the order preservation of Ψ2ε . For the estimates, nonzero weight
gives
                               Jε (x) − hε ℓ = hε z   (z ∈ ZA,P ).
Fix a ∈ A and a nonempty upper set U ⊆ P, and write λ = λa,U . Using
                                  Jε (x) = (1 − ε)x + εu,      hε = cε,
and the linearity of λ, we obtain
                                 λ(hε ℓ) = (1 − ε)λ(x) + ελ(u) − cελ(z).
Since
                             0 ≤ λ(x), λ(u) ≤ 1,         0 ≤ λ(z) ≤ RA,P ,
it follows that
                        λ(hε ℓ) ≥ (1 − ε)λ(x) − cεRA,P ≥ λ(x) − ε − cεRA,P ,
                        λ(hε ℓ) ≤ (1 − ε)λ(x) + ε ≤ λ(x) + ε.
Hence
                             λ(x) − ε − cεRA,P ≤ λ(hε ℓ) ≤ λ(x) + ε.
Using equation (20) with t = 2ε, we obtain
                                                          +
                                  λ(yε (ℓ)) ≤ λ(hε ℓ) − 2ε ,
                                                             +
                                  λ(yε (ℓ)) ≥ λ(hε ℓ) − 2KP ε .
Since
                             λ(x) − ε − cεRA,P ≤ λ(hε ℓ) ≤ λ(x) + ε,
                                                   27


---

and since r 7→ r+ is monotone, it follows that
                                                         +
                                     λ(yε (ℓ)) ≤ λ(x) − ε ,
                                                            +
                                     λ(yε (ℓ)) ≥ λ(x) − C∗ ε ,
where
                                       C∗ = 1 + 2KP + cRA,P .
Now set
                                          ε
                                      αε =  ,     βε = C∗ ε.
                                         KP
Applying equation (20) to x with parameters t = αε and t = βε , respectively, gives
                                              +
                                     λ(x) − ε ≤ λ(Ψαε (x))
and
                                                             +
                                     λ(Ψβε (x)) ≤ λ(x) − C∗ ε .
Hence
                                λ(Ψβε (x)) ≤ λ(yε (ℓ)) ≤ λ(Ψαε (x)).
Since the functionals λa,U determine the order on M(A, P), we conclude that
                                      Ψβε (x) ≤ yε (ℓ) ≤ Ψαε (x).


   A probability kernel on K is a Scott-continuous map k : K −→ V1 (K). In this paper, such a
kernel is called finite if there are a finite poset L and Scott-continuous maps
                                         p           V1 (y)
                                      K→
                                       − V1 (L) −−−−→ V1 (K)
with y : L → K and k = V1 (y) ◦ p. For a finite probability vector ℓ rℓ δℓ and labels yℓ ∈ K, the
                                                                           P
pushforward algong y is Σℓ rℓ δyℓ , and its barycentre is ℓ rℓ yℓ . Since K is convex and contains the
                                                         P
zero map, the same formula defines a point of K for a subprobability vector, with the missing mass
placed at zero. Define
                                                              X
                            eε : V≤1 (Lε ) −→ K, eε (ν) =           νℓ yε (ℓ),                    (31)
                                                                ℓ∈Lε

                             κε = V1 (yε )pε : K −→ V1 (K),                                       (32)
                             dε = eε pε : K −→ K.                                                 (33)
Thus κε (x) is the finite probability distribution obtained by replacing each grid state ℓ by its label
yε (ℓ), and dε (x) is its barycentre. In equation (31), if ν has total mass less than one, the missing
mass is placed at the zero map of K; this does not change the displayed sum.
Proposition 9.2. The maps in equations (31) to (33) are Scott-continuous and, for every x ∈ K,
                                      δΨβε (x) ≤ κε (x) ≤ δΨαε (x) ,                              (34)
                                      Ψβε (x) ≤ dε (x) ≤ Ψαε (x).                                 (35)
The kernel κε factors through V1 (Lε ), and dε factors through V≤1 (Lε ).


                                                   28


---

Proof. For every a ∈ A and every nonempty U ∈ Up(P), the map ℓ 7−→ λa,U (yε (ℓ)) is nonnegative
and monotone. Hence, by lemma 2.2, the map eε is monotone. It is Euclidean-continuous and
therefore Scott-continuous by lemma 7.3. Consequently, the Scott continuity of κε and dε follows
from their respective factorizations
                                 κε = V1 (yε ) ◦ pε ,              dε = eε ◦ pε .
   We first record a simple consequence of the stochastic order. Suppose that
                                        a ≤ xi ≤ b              (1 ≤ i ≤ n),
and let (ri )ni=1 be a probability vector. If X is a random variable satisfying P(X = xi ) = ri , then
a ≤ X ≤ b almost surely. Thus (a, X) and (X, b) are monotone couplings, and hence
                                            X n
                                       δa ≤     ri δ xi ≤ δb .
                                                     i=1
    Now fix x ∈ K. By equation (30), every ℓ ∈ supp(pε (x)) satisfies Ψβε (x) ≤ yε (ℓ) ≤ Ψαε (x). Ap-
                                                                                                
plying the preceding observation to the probability vector pε (x)({ℓ}) ℓ∈Lε and the family yε (ℓ) ℓ∈Lε ,
we obtain                                X
                              δΨβε (x) ≤    pε (x)({ℓ}) δyε (ℓ) ≤ δΨαε (x) .
                                            ℓ∈Lε
Since                                              X
                                        κε (x) =          pε (x)({ℓ}) δyε (ℓ) ,
                                                   ℓ∈Lε
this proves equation (34).
    Similarly, for every a ∈ A and every nonempty U ∈ Up(P), the linearity of λa,U gives
                            X
               λa,U Ψβε (x) ≤     pε (x)({ℓ})λa,U yε (ℓ) = λa,U dε (x) ≤ λa,U Ψαε (x) .
                                                                                   
                               ℓ∈Lε

Since the coordinates λa,U , with a ∈ A and ∅ , U ∈ Up(P), determine the order on K, it follows
that
                                       Ψβε (x) ≤ dε (x) ≤ Ψαε (x),
which is equation (35).
    Finally, κε = V1 (yε ) ◦ pε is the asserted finite-kernel factorization, while dε = eε ◦ pε is the
asserted factorization through V≤1 (Lε ).
   For a single value of ε, the preceding proposition gives only a one-step approximation. We
now choose a geometric sequence of scales so that the upper bound at level n lies below the
lower bound at level n + 1. This produces genuinely increasing approximations rather than merely
approximations converging in Euclidean distance.
Proposition 9.3. There are finite posets Ln and Scott-continuous maps
                    pn : K → V1 (Ln ),          yn : Ln → K,                en : V≤1 (Ln ) → K
such that, with
                                      κn = V1 (yn )pn ,            dn = en pn ,

                                                           29


---

one has
                                  κn ≤ κn+1 ≤ ηK ,         sup κn = ηK ,                          (36)
                                                            n
                                  dn ≤ dn+1 ≤ idK ,        sup dn = idK .                         (37)
                                                                n
Each κn factors through V1 (Ln ), and each dn is a finite-valuation approximant.
Proof. Choose constants
                                                                         ( )
                                  1                                1 1
                         0 < ε0 <             and      0 < θ < min ,         .
                                  2                                2 KPC ∗
For every n ≥ 0, set
               εn = ε0 θn ,     Ln = Lεn ,          pn = pεn ,          yn = yεn ,   en = eεn ,
and let
                                         κn = κεn ,        dn = dεn .
Also write
                                         εn
                                       αn = ,              βn = C∗ εn .
                                         KP
Since εn+1 = θεn and θ < 1/(KPC∗ ), we have
                                                          εn
                                 βn+1 = C∗ εn+1 = C∗ θεn <     = αn .
                                                         KP
The family (Ψt )t≥0 is decreasing in t; hence Ψαn (x) ≤ Ψβn+1 (x) for any x ∈ K. By equations (34)
and (35), for every n and every x ∈ K,
                                      δΨβn (x) ≤ κn (x) ≤ δΨαn (x) ≤ δ x
and
                                 Ψβn (x) ≤ dn (x) ≤ Ψαn (x) ≤ x.
Combining these inequalities with Ψαn (x) ≤ Ψβn+1 (x) gives
                              κn (x) ≤ δΨαn (x) ≤ δΨβn+1 (x) ≤ κn+1 (x) ≤ δ x ,
                              dn (x) ≤ Ψαn (x) ≤ Ψβn+1 (x) ≤ dn+1 (x) ≤ x.
Thus (κn )n and (dn )n are pointwise increasing, with κn ≤ ηK and dn ≤ idK for every n.
    We next identify their pointwise suprema. Since βn = C∗ ε0 θn → 0,, we have supn Ψβn (x) = x for
any x ∈ K. Using the lower half of equation (35), we have Ψβn (x) ≤ dn (x) ≤ x. Taking suprema over
n yields
                                   x = sup Ψβn (x) ≤ sup dn (x) ≤ x.
                                          n                 n
Therefore supn dn (x) = x for any x ∈ K, and hence supn dn = idK pointwise.
   Similarly, equation (34) gives
                                      ηK (Ψβn (x)) ≤ κn (x) ≤ ηK (x).
Since the Dirac unit
                                  ηK : K −→ V1 (K),                 x 7−→ δ x ,

                                                      30


---

is Scott-continuous, it preserves the directed supremum supn Ψβn (x) = x. Consequently,
                                                              !
                             sup ηK (Ψβn (x)) = ηK sup Ψβn (x) = ηK (x).
                              n                         n
Taking suprema gives
                                     ηK (x) ≤ sup κn (x) ≤ ηK (x),
                                               n
and hence supn κn (x) = ηK (x) for any x ∈ K. Thus supn κn = ηK pointwise.
    Finally, by the definitions in equations (31) and (32), each κn and dn factors through the finite
poset Ln :
                                 κn = V1 (yn ) ◦ pn ,   dn = en ◦ pn .
Hence (κn )n is an increasing finite-kernel approximation of ηK , and (dn )n is an increasing finite-
valuation approximate identity on K.
Theorem 9.4. For all finite posets A, P, M(A, P) ∈ ωFVA.
Proof. If A = ∅ or P = ∅, the dcpo is a singleton and hence belongs to ωFVA by lemma 6.4.
Otherwise, lemma 7.1 and proposition 9.3 gives a finite-valuation approximate identity (dn ).
     The finite-dimensional part is now complete. Every finite monotone-valuation polytope has an
increasing approximate identity through valuation spaces of finite posets, and it also carries finite
kernels converging increasingly to the Dirac unit. The latter, stronger statement is the input for the
lifting arguments in the next section.
     A finite kernel approximation of the Dirac unit is stronger than an ordinary approximation
of points. The valuation monad can integrate such a kernel against an arbitrary input valuation,
thereby producing an approximation of the whole valuation powerdomain. The same kernel can
also replace the input of a function by a finite probabilistic mixture, producing an approximation of
a function space. This section formulates both operations as one lifting principle.
     We record the two local-continuity properties used in the lifting argument. They follow directly
from the continuous-valuation calculus of Jones and Plotkin [9, 10]. We include short proofs to
make the directed-supremum computations explicit.
Lemma 9.5. Let ( fi )i∈I be a directed family of Scott-continuous maps fi : D → E, and let f = supi fi
pointwise. Then V≤1 ( f ) = supi V≤1 ( fi ), where the supremum on the right is taken pointwise in
[V≤1 (D) → V≤1 (E)].
   In particular, if fi ≤ idD for every i ∈ I and supi fi = idD , then V≤1 ( fi ) ≤ idV≤1 (D) , and
supi V≤1 ( fi ) = idV≤1 (D) .
Proof. Jones and Plotkin define the action of the valuation functor on a Scott-continuous map
g : D → E by
                                  V≤1 (g)(ν) (U) = ν(g−1 (U))
                                            

for every ν ∈ V≤1 (D) and every Scott-open set U ⊆ E. Directed suprema of valuations are
computed pointwise on Scott-open sets [10, Theorem 2.1].



                                                   31


---

   Fix ν ∈ V≤1 (D) and a Scott-open set U ⊆ E. The family fi−1 (U) i∈I is directed under inclusion.
                                                                  
Indeed, if fi , f j ≤ fk , then the upperness of U gives
                                              fi−1 (U) ∪ f j−1 (U) ⊆ fk−1 (U).
Moreover,                                                      [
                                                  f −1 (U) =         fi−1 (U).
                                                               i∈I
One inclusion follows from fi ≤ f and the upperness of U. Conversely, if f (x) ∈ U, then
                                                      f (x) = sup fi (x),
                                                                i
and Scott openness of U implies that fi (x) ∈ U for some i ∈ I. By the continuity of the valuation ν,
                                                     
                                        [ −1 
      V≤1 ( f )(ν) (U) = ν f (U) = ν 
                            −1
                                              fi (U) = sup ν fi−1 (U) = sup V≤1 ( fi )(ν) (U).
                                                                                         
                                                      i                    i             i

Since this holds for every ν ∈ V≤1 (D) and every Scott-open U ⊆ E, it follows that V≤1 ( f ) =
supi V≤1 ( fi ).
     Now suppose that fi ≤ idD . For every Scott-open U ⊆ D, fi−1 (U) ⊆ U, because fi (x) ∈ U and
fi (x) ≤ x imply x ∈ U. Therefore
                                V≤1 ( fi )(ν) (U) = ν fi−1 (U) ≤ ν(U),
                                                             

and hence V≤1 ( fi ) ≤ idV≤1 (D) . Finally, applying the first part to supi fi = idD gives
                                                       !
                         sup V≤1 ( fi ) = V≤1 sup fi = V≤1 (idD ) = idV≤1 (D) .
                               i                           i



Lemma 9.6. Let (ki )i∈I be a directed family of Scott-continuous kernels ki : D → V≤1 (E) with
pointwise supremum k. Then ki† ↑ k† . If E = D and ki ≤ ηD , then ki† ≤ idV≤1 (D) .
Proof. Fix ν ∈ V≤1 (D) and a Scott-open set U ⊆ E. Put
                                     gi (x) = ki (x)(U),             g(x) = k(x)(U).
Evaluation at U is Scott-continuous on V≤1 (E). Hence the gi are upper-continuous functions in the
terminology of [9], the family (gi )i∈I is directed, and
                                                      g(x) = sup gi (x)
                                                                i
for every x ∈ D. Moreover, g is bounded by 1. Jones’s directed monotone-convergence theorem [9,
Theorem 3.13] therefore gives
              Z                   Z                           Z
   (k ν)(U) =
     †
                 k(x)(U) dν(x) =    sup ki (x)(U) dν(x) = sup   ki (x)(U) dν(x) = sup(ki† ν)(U).
                 D                            D   i                              i   D       i
Directed suprema in V≤1 (E) are computed pointwise on Scott-open sets. Thus
                                                       k† ν = sup ki† ν.
                                                                i

Since ν was arbitrary, k   †
                               = supi ki† .
                                                               32


---

      Now suppose that E = D and ki ≤ ηD . For every ν ∈ V≤1 (D) and every Scott-open U ⊆ D,
                          Z                   Z
              (ki ν)(U) =
                †
                            ki (x)(U) dν(x) ≤    ηD (x)(U) dν(x) = (η†D ν)(U) = ν(U),
                             D                    D

where the last equality is the Kleisli unit law ηD = idV≤1 (D) . Hence ki† ≤ idV≤1 (D) .
                                                 †


    Recall that ηX : X → V1 (X) is the unit of the continuous valuation monad, sending each x ∈ X
to the Dirac valuation δ x .
Theorem 9.7. Let X be an FS-domain. Suppose that there are finite posets Ln and Scott-continuous
maps
                             pn : X → V1 (Ln ),    yn : Ln → X
such that
                    κn = V1 (yn )pn ,  κn ≤ κn+1 ≤ ηX ,      sup κn = ηX .
                                                                        n
Then
  (i) V≤1 (X) ∈ ωFVA;
 (ii) [X → V≤1 (P)] ∈ ωFVA for every finite poset P.
Proof. The dcpo V≤1 (X) is a continuous domain. For each n, define
                                     T n = κn† : V≤1 (X) −→ V≤1 (X).
By lemma 9.6,
                      T n ≤ T n+1 ≤ idV≤1 (X)    and        sup T n = η†X = idV≤1 (X) .
                                                              n
Moreover, since κn = V≤1 (yn ) ◦ pn , the Kleisli associativity law yields
                                                       †
                           T n = κn† = V≤1 (yn ) ◦ pn = V≤1 (yn ) ◦ p†n .
Thus each T n factors as
                                           p†n           V≤1 (yn )
                                V≤1 (X) −−−→ V≤1 (Ln ) −−−−−−→ V≤1 (X).
Since Ln is finite, this gives the required finite-valuation approximation of the identity on V≤1 (X),
and proves (i).
   For (ii), the assertion is immediate when P = ∅. Assume P , ∅ and put Y = V≤1 (P). Since X
and Y are FS-domains, [X → Y] is an FS-domain. Let Bn be the set of monotone maps from Ln to
Y with pointwise order, i.e.,
                                             Bn = M(Ln , P).
An element of Bn is a finite monotone table assigning a target valuation to each state of Ln . By
theorem 9.4, Bn ∈ ωFVA. Define
                                 Pn : [X → Y] → Bn ,       Pn ( f ) = f ◦ yn ,
and
                            En : Bn → [X → Y],        En (v) = v† ◦ pn .
The map Pn samples f at the finitely many labels yn (ℓ). The map En reconstructs a function by
encoding x as the distribution pn (x) and then taking the corresponding probabilistic mixture of
                                                    33


---

the table values v(ℓ). The map Pn is Scott-continuous by pointwise evaluation. The map En is
Scott-continuous by lemma 9.6. For An = En Pn , the monad laws give
                                        An ( f )(x) = f † (κn (x)).
Consequently
                            An ≤ An+1 ≤ id[X→Y] ,         sup An = id[X→Y] .
                                                            n
Each An factors through Bn ∈ ωFVA, so theorem 6.7(ii) applies.
Corollary 9.8. For all finite posets P, Q,
                   V≤1 (V≤1 (Q)) ∈ ωFVA,            [V≤1 (Q) → V≤1 (P)] ∈ ωFVA.
Proof. If Q = ∅, then V≤1 (Q) is terminal, so both assertions hold. If Q , ∅, apply proposition 9.3
and theorem 9.7 to X = V≤1 (Q) = M(1, Q).
    We have now established the two finite-generator statements needed later: a second application
of the valuation functor and a function space between two finite valuation generators both belong to
ωFVA. It remains to treat products of finite generators and then transfer all three constructions to
general objects.

10. ωFVA as a solution to Jung–Tix Problem
    We now prove that ωFVA is a full Cartesian closed subcategory of continuous domains and is
closed under both the subprobability and probability valuation powerdomains. This gives a solution
to the generalized Jung–Tix problem.
    A product of two finite valuation generators is not itself presented in the form V≤1 (R) by
definition. We place it inside one such generator as a Scott-continuous retract. We use the ordinary
product of finite probability distributions for the embedding and the two marginals for the retraction.
Proposition 10.1. For finite posets P, Q, the product V≤1 (P) × V≤1 (Q) is a Scott-continuous retract
of V≤1 (R) for a finite poset R. Consequently V≤1 (P) × V≤1 (Q) ∈ ωFVA.
                                             b = P⊥ , Q
Proof. Adjoin fresh least elements and write P        b = Q⊥ . By proposition 5.4, adding missing
mass at the new least element gives order isomorphisms
                             V≤1 (P)  V1 (P),
                                           b      V≤1 (Q)  V1 (Q).
                                                                  b
Let
                                      R = (Pb × Q)
                                                b \ {(⊥, ⊥)}.
A further application of proposition 5.4 gives
                                      V≤1 (R)  V1 (Pb × Q).
                                                         b
Define
                     E : V1 (P)
                             b × V1 (Q)
                                     b −→ V1 (P
                                              b × Q),
                                                  b                   E(µ, ν) = µ ⊗ ν,
and
                                                            M(ξ) = V1 (π1 )(ξ), V1 (π2 )(ξ) .
                                                                                           
            M : V1 (P
                    b × Q)
                        b −→ V1 (P)
                                 b × V1 (Q),
                                         b

                                                   34


---

Here (µ ⊗ ν)(x,y) = µ x νy , and π1 , π2 are the coordinate projections. The marginals of a product
distribution are the original factors, so M ◦ E = id.
    The marginal maps are monotone because they are pushforwards along monotone maps. To
prove monotonicity of E, let µ ≤st µ′ and ν ≤st ν′ , and let W ⊆ P  b× Q
                                                                       b be upper. For x ∈ P,
                                                                                           b put
                                        W x = {y ∈ Q
                                                   b : (x, y) ∈ W}.
                     b and the function x 7→ ν(W x ) is nonnegative and monotone. Hence lemma 2.2
Each W x is upper in Q,
gives                              X                 X
                      (µ ⊗ ν)(W) =     µ x ν(W x ) ≤    µ′x ν(W x ) = (µ′ ⊗ ν)(W).
                                          x                   x
Furthermore, ν(W x ) ≤ ν (W x ) for every x, and therefore
                          ′

                                         (µ′ ⊗ ν)(W) ≤ (µ′ ⊗ ν′ )(W).
Thus E(µ, ν) ≤st E(µ′ , ν′ ).
    Both E and M are Euclidean-continuous. By lemma 7.3, they are Scott-continuous. Transporting
this retraction across the displayed order isomorphisms makes V≤1 (P) × V≤1 (Q) a Scott-continuous
retract of V≤1 (R). The final assertion follows from lemma 6.4 and corollary 6.9.
    The finite-generator analysis is now closed under the three operations that will appear globally:
products, function spaces, and one further application of V≤1 . We now transport these finite
results along the approximate identities of arbitrary objects of ωFVA. For a general object X ∈
ωFVA, an approximate identity first compresses X through spaces V≤1 (Pn ). Applying a product,
function-space, or valuation construction to these compressions yields approximations through the
corresponding finite-generator objects established above. The saturation theorem then flattens those
intermediate approximations back to a finite-valuation approximate identity. The three parts of the
next theorem are instances of this same transfer pattern.
Theorem 10.2. Let X, Y ∈ ωFVA. Then
   (i) X × Y ∈ ωFVA;
  (ii) [X → Y] ∈ ωFVA;
 (iii) V≤1 (X) ∈ ωFVA.
Proof. Choose finite-valuation approximate identities
                              an = enX pnX : X → X,               bn = eYn pYn : Y → Y,
through V≤1 (Pn ) and V≤1 (Qn ), respectively.
    For (i), put cn = an × bn . Then
                                                                                          !
                cn ≤ cn+1 ≤ idX×Y ,             sup cn (x, y) = sup an (x), sup bn (y) = (x, y).
                                                 n                   n               n
Moreover, cn factors as
                                     pnX ×pYn                             enX ×eYn
                              X × Y −−−−→ V≤1 (Pn ) × V≤1 (Qn ) −−−−→ X × Y.
The intermediate object belongs to ωFVA by proposition 10.1. Applying theorem 6.7(ii) proves (i).


                                                         35


---

   For (ii), theorem 6.7(i) shows that X and Y are FS-domains, so [X → Y] is an FS-domain.
Define
                     An : [X → Y] −→ [X → Y],        An ( f ) = bn ◦ f ◦ an .
For f ∈ [X → Y] and x ∈ X,
              An ( f )(x) = bn ( f (an (x))) ≤ bn+1 ( f (an (x))) ≤ bn+1 ( f (an+1 (x))) = An+1 ( f )(x),
and An ( f )(x) ≤ f (x). Thus An ≤ An+1 ≤ id.
    The family
                                        {b j ◦ f ◦ ai : (i, j) ∈ N2 }
is directed, and its diagonal is cofinal. Therefore, using first sup j b j = idY and then Scott continuity
of f ,                                                                            !
                sup An ( f )(x) = sup b j ( f (ai (x))) = sup f (ai (x)) = f sup ai (x) = f (x).
                  n                  i, j                     i                       i
Define
                 Rn : [X → Y] −→ [V≤1 (Pn ) → V≤1 (Qn )],                       Rn ( f ) = pYn ◦ f ◦ enX ,
and
                S n : [V≤1 (Pn ) → V≤1 (Qn )] −→ [X → Y],                    S n (k) = eYn ◦ k ◦ pnX .
Directed suprema in function spaces are computed pointwise, so composition on either side by
a fixed Scott-continuous map preserves them. Hence Rn and S n are Scott-continuous. A direct
calculation gives
                         S n Rn ( f ) = (eYn pYn ) ◦ f ◦ (enX pnX ) = bn ◦ f ◦ an = An ( f ).
Thus An factors through [V≤1 (Pn ) → V≤1 (Qn )] ∈ ωFVA by corollary 9.8. Applying theorem 6.7(ii)
proves (ii).
    For (iii), V≤1 (X) is a domain. By lemma 9.5,
                      V≤1 (an ) ≤ V≤1 (an+1 ) ≤ idV≤1 (X) ,           sup V≤1 (an ) = idV≤1 (X) .
                                                                        n
Functoriality gives the factorization
                                            V≤1 (pnX )                  V≤1 (enX )
                              V≤1 (X) −−−−−−→ V≤1 (V≤1 (Pn )) −−−−−→ V≤1 (X),
whose composite is V≤1 (an ). By corollary 9.8, the intermediate object belongs to ωFVA. A final
application of theorem 6.7(ii) proves (iii).
      The terminal one-point dcpo is V≤1 (∅), hence belongs to ωFVA.
Theorem 10.3. If D ∈ ωFVA, then V1 (D) ∈ ωFVA.
Proof. Let ⊥ be the least element of D, which exists by lemma 6.4. Define
                                                 jD : V1 (D) −→ V≤1 (D)
to be the inclusion and
                        ND : V≤1 (D) −→ V1 (D),                   ND (ν) = ν + (1 − ν(D))δ⊥ .
The displayed valuation has total mass one. If U ⊊ D is Scott open, then ⊥ < U, and hence
                                                     ND (ν)(U) = ν(U),
                                                            36


---

whereas ND (ν)(D) = 1. These formulas show directly that ND is monotone. If (νi )i is directed with
supremum ν, then for every proper Scott-open U,
                           ND (ν)(U) = ν(U) = sup νi (U) = sup ND (νi )(U),
                                                        i                i
and the same equality is immediate for U = D, where all values are 1. Hence ND is Scott-continuous,
ND jD = idV1 (D) , and V1 (D) is a Scott-continuous retract of V≤1 (D). Apply theorem 10.2(iii) and
corollary 6.9.
Theorem 10.4. Let ωFVA be the full subcategory of DCPO defined in definition 6.2. Then:
   (i) every object of ωFVA is a pointed countably based FS-domain;
  (ii) V≤1 (P) ∈ ωFVA for every finite poset P, and ωFVA contains the terminal dcpo and is closed
       under Scott-continuous retracts and finite products;
 (iii) X, Y ∈ ωFVA implies [X → Y] ∈ ωFVA;
 (iv) D ∈ ωFVA implies V≤1 (D), V1 (D) ∈ ωFVA.
Hence ωFVA is a full Cartesian closed subcategory of FS, and both valuation monads restrict to
ωFVA.
Proof. Assertion (i) follows from lemma 6.4, theorem 6.7, and proposition 6.8. Assertion (ii)
follows from lemma 6.4, corollary 6.9, and theorem 10.2, since the terminal dcpo is V≤1 (∅).
Assertion (iii) is theorem 10.2(ii), and assertion (iv) follows from theorem 10.2(iii) and theorem 10.3.
Since ωFVA is full, the evaluation and currying maps of DCPO are morphisms in ωFVA, so ωFVA
is Cartesian closed. The units and multiplications of the subprobability and probability valuation
monads are Scott-continuous maps between objects of ωFVA and therefore belong to the full
subcategory.
   This gives a solution to the generalized Jung–Tix problem.
Remark 10.5. Countable basedness is not necessary in the definition of ωFVA. There is also a
nonsequential version of the construction. Let FVA denote the full replete subcategory of DCPO
whose objects are the domains D admitting a directed family (ai )i∈I with
                                           ai = ei ◦ pi : D → D,
of finite-valuation approximants such that ai ≤ idD and supi∈I ai = idD pointwise. Then
                                                ωFVA ⊆ FVA,
and no countability condition is imposed on the objects of FVA.
    The preceding proofs extend to FVA with only the following changes. In the square-refinement
argument, one retains the directed family of squares and omits the final extraction of a countable
cofinal sequence. The saturation proof remains valid because every comparison involves only finitely
many approximants, and directedness provides a common upper bound for the corresponding finitely
many indices. For products, if (ai )i∈I and (b j ) j∈J approximate the identities of X and Y, respectively,
one uses the product-directed family
                                               (ai × b j )(i, j)∈I×J .
For function spaces one uses
                                Ai, j ( f ) = b j ◦ f ◦ ai ,        (i, j) ∈ I × J,
                                                            37


---

so that no diagonal or countable cofinality argument is required. For the subprobability power-
domain one uses the directed family V≤1 (ai ) i∈I , and the probability case follows from the same
                                               
missing-mass retraction V1 (D) ◁ V≤1 (D).
    Consequently, after deleting the countable-basis conclusion, the same finite-generator, saturation,
and transfer arguments show that FVA is a full Cartesian closed subcategory of DCPO and that
                             D ∈ FVA         =⇒       V≤1 (D), V1 (D) ∈ FVA.
Hence both the subprobability and probability valuation monads restrict to FVA.

11. Comparison with bc-domains and RB-domains
    Recall that a bc-domain is a pointed domain in which every bounded subset has a supremum. We
write BC for the category of bc-domains and ωBC for the category of countably based bc-domains.
An RB-domain is a Scott-continuous retract of a bifinite domain; equivalently, its identity is the
directed supremum of finite-image Scott-continuous self-maps below the identity. We write RB for
this full category. Let ωFS⊥ denote the full subcategory of pointed countably based FS-domains.
Lemma 11.1. Every finite bc-domain belongs to ωFVA.
Proof. Let B be a finite bc-domain, let N = |B|, and put
                                                     1
                                          τ=1−           .
                                                   N+1
Since B has a least element, proposition 5.4 and lemma 6.4 gives
                                   V1 (B)  V≤1 (B \ {⊥}) ∈ ωFVA.
For µ ∈ V1 (B), define
                                                S (µ) = {b ∈ B : µ(↑b) > τ}.
Viewing µ as a probability vector on the finite set B, one has
                                       
                         \                   X                         |S (µ)|     1
                   µ                                  1 − µ(↑b) > 1 −                  > 0.
                                                                   
                                   ↑b ≥ 1 −                                      ≥
                           b∈S (µ)                b∈S (µ)
                                                                             N+1 N+1
                                                                                               W
Thus S (µ) has a common upper bound. Since B is bounded complete, the join S (µ) exists; for
S (µ) = ∅ it is understood to be ⊥. Define
                                                                              _
                                          rB : V1 (B) −→ B,         rB (µ) =      S (µ).
If µ ≤st ν, then S (µ) ⊆ S (ν), and hence rB (µ) ≤ rB (ν). Moreover, if (µi )i∈I is directed with supremum
µ, then, for every b ∈ B,
                                           µ(↑b) = sup µi (↑b),
                                                         i
so                                                     [
                                             S (µ) =         S (µi ).
                                                         i
Consequently,                                _[                    _
                                  rB (µ) =             S (µi ) =        rB (µi ),
                                                  i                 i
                                                       38


---

and rB is Scott-continuous. Finally,
                                 S (δ x ) = ↓x,       rB (δ x ) = x       (x ∈ B).
Thus rB ◦ ηB = idB , so B is a Scott-continuous retract of V1 (B). The conclusion follows from
corollary 6.9.
Proposition 11.2. Every countably based bc-domain belongs to ωFVA.
Proof. Let D be a countably based bc-domain. By the standard inclusion BC ⊆ RB, there is a
directed family ( fi )i∈I of finite-image Scott-continuous maps such that
                                         fi ≤ idD ,       sup fi = idD .
                                                              i
We first replace this family by an increasing sequence. Let B0 be a countable basis of D, and
enumerate all pairs
                               (b, c) ∈ B0 × B0        with     b ≪ c.
For every such pair, the equality c = supi fi (c) yields an index i with b ≤ fi (c). Using directedness,
choose recursively an increasing sequence (gn )n from the family ( fi )i that satisfies the first n of these
requirements. If y ≪ x, interpolation and the basis property give b, c ∈ B0 such that
                                                  y ≤ b ≪ c ≤ x.
For all sufficiently large n,
                                           y ≤ b ≤ gn (c) ≤ gn (x).
It follows that
                                     gn ≤ gn+1 ≤ idD ,            sup gn = idD .
                                                                   n
    Fix n and let Fn = gn [D]. A bc-domain has all nonempty infima: the infimum of a nonempty
set is the supremum of its set of lower bounds. Let Cn be the closure of the finite set Fn under
nonempty infima. Then Cn is finite, contains ⊥, and is closed under finite nonempty meets. Hence
Cn is a finite bc-domain: if A ⊆ Cn has an upper bound in Cn , then
                             _      ^
                                A=     {c ∈ Cn : a ≤ c for every a ∈ A}.
                                Cn

By lemma 11.1, Cn ∈ ωFVA.
    Regard gn as a map pn : D → Cn , and let en : Cn ,→ D be the inclusion. To see that pn is
Scott-continuous, let A ⊆ D be directed. The directed set gn [A] ⊆ Fn is finite and therefore has a
largest element m. Since gn : D → D is Scott-continuous,
                         pn (sup A) = gn (sup A) = sup gn [A] = m = sup pn [A].
                                                                               Cn

The inclusion en is Scott-continuous because every directed subset of the finite poset Cn has a
largest element, which is its supremum both in Cn and in D. Moreover,
                                                   gn = en ◦ pn .
Thus the increasing approximate identity (gn )n factors through objects Cn ∈ ωFVA. Applying
theorem 6.7(ii) gives D ∈ ωFVA.

                                                         39


---

Lemma 11.3. If a finite domain D belongs to ωFVA, then D is a Scott-continuous retract of V≤1 (P)
for some finite poset P.
Proof. Let (an )n be a finite-valuation approximate identity on D, with
                                                       pn              en
                                an = en pn ,        D −→ V≤1 (Pn ) −→ D.
For each x ∈ D, the increasing sequence (an (x))n has supremum x. Since D is finite, it is eventually
equal to x. As D has only finitely many elements, there is one index N such that
                                        aN (x) = x          (x ∈ D).
Thus eN pN = idD , and the displayed factorization at index N is the required Scott-continuous
retraction.
Lemma 11.4. Let P be a finite poset. The Scott topology on V≤1 (P) is coarser than the relative
Euclidean topology. Consequently, every convex subset of V≤1 (P) is connected in its relative Scott
topology.
Proof. Let O ⊆ V≤1 (P) be Scott open and let µ ∈ O. For n ≥ 1, put
                                               µn = (1 − 2−n )µ.
Then µn ↑ µ, so µn ∈ O for some n. Since O is an upper set,
                                                  ↑µn ⊆ O.
The stochastic order on V≤1 (P) is determined by upper-set coordinates:
                      ν ∈ ↑µn     ⇐⇒       ν(U) ≥ µn (U) for every U ∈ Up(P).
If µ(U) > 0, then
                                           µ(U) > µn (U),
whereas if µ(U) = 0, the inequality ν(U) ≥ µn (U) = 0 is automatic. Since Up(P) is finite and
every map ν 7→ ν(U) is linear, ↑µn contains a relative Euclidean neighborhood of µ. Hence every
Scott-open subset of V≤1 (P) is relatively Euclidean open.
   A convex subset of a real vector space is Euclidean connected. Its relative Scott topology is
coarser than its relative Euclidean topology, and is therefore connected as well.
Proposition 11.5. Let
                                          B5 = {⊥, a, b, c, d},
where
                      ⊥ < a < c, d,     ⊥ < b < c, d,              a ∥ b,   c ∥ d,
and there are no further comparabilities. Then
                                           B5 ∈ RB \ ωFVA.
Proof. The poset B5 is finite and pointed. Hence its identity is an idempotent finite-image deflation,
and therefore B5 ∈ RB.


                                                      40


---

   Suppose, towards a contradiction, that B5 ∈ ωFVA. By lemma 11.3, there are a finite poset P
and Scott-continuous maps
                                   i          r
                                B5 →
                                   − V≤1 (P) → − B5 ,       r ◦ i = idB5 .
Consider the set of common upper bounds of i(a) and i(b),
                              H = {ν ∈ V≤1 (P) : i(a) ≤ ν and i(b) ≤ ν}.
The set H is convex: each of its defining conditions is a finite family of linear inequalities in the
upper-set coordinates. It is therefore connected in its relative Scott topology by lemma 11.4.
    For every ν ∈ H, monotonicity of r gives
                              a = r(i(a)) ≤ r(ν),     b = r(i(b)) ≤ r(ν).
The only common upper bounds of a and b in B5 are c and d. Consequently,
                                             r[H] ⊆ {c, d}.
Conversely, i(c), i(d) ∈ H and
                                     r(i(c)) = c,     r(i(d)) = d,
so
                                             r[H] = {c, d}.
Since c and d are incomparable maximal elements, {c, d} is discrete, and hence disconnected, in its
relative Scott topology. This contradicts the fact that the continuous image of the connected space
H under r|H must be connected. Therefore B5 < ωFVA.
Theorem 11.6. We have ωBC ⊊ ωFVA ⊊ ωFS⊥ . Moreover, ωFVA and RB are incomparable:
                           ωFVA ⊈ RB,     RB ⊈ ωFVA.
Proof. The first inclusion is proposition 11.2, and the second follows from theorem 10.4(i).
    Let
                          D4 = {⊥, a, b, ⊤},      ⊥ < a, b < ⊤,     a ∥ b,
be the four-element diamond. By proposition 5.4 and lemma 6.4,
                                 V1 (D4 )  V≤1 (D4 \ {⊥}) ∈ ωFVA.
On the other hand, the finite-poset classification of [3] gives
                                            V1 (D4 ) < RB,
because the undirected Hasse graph of D4 is not a tree. Since every bc-domain is an RB-domain,
this also proves
                             ωBC ⊊ ωFVA           and      ωFVA ⊈ RB.
    Finally, proposition 11.5 gives
                                          B5 ∈ RB \ ωFVA,
and therefore RB ⊈ ωFVA.
Remark 11.7. The countability qualifier in the inclusion ωBC ⊆ ωFVA remains essential, because
every object of ωFVA is countably based. By contrast, the failure RB ⊈ ωFVA is not a cardinality
phenomenon: proposition 11.5 witnesses it by a finite RB-domain. Thus the incomparability of
ωFVA and RB already occurs among pointed countably based FS-domains.
                                                  41


---

Acknowledgment
    During the preparation of this manuscript, the authors used AI-assisted tools for language polish-
ing and grammar checking. The authors carefully reviewed and verified the final manuscript and take
full responsibility for its content, including the correctness of all mathematical statements, proofs,
and references. The Lean 4 formalization will be released in https://github.com/ChanYuxu/Recent-
Progress-on–Domain-Theory.

References
 [1] S. Abramsky and A. Jung, Domain theory, in S. Abramsky, D. M. Gabbay and T. S. E.
     Maibaum (eds.), Handbook of Logic in Computer Science, Vol. 3, Oxford University Press,
     Oxford, 1994.

 [2] G. Berry, Stable models of typed lambda-calculi, in G. Ausiello and C. Böhm (eds.), Automata,
     Languages and Programming, Lecture Notes in Computer Science 62, Springer, Berlin, 1978,
     pp. 72–89.

 [3] Y. Chen, H. Kou and Z. Lyu, Characterizing finite posets whose probabilistic powerdomains
     are RB-domains, arXiv:2607.02231, 2026.

 [4] G. Gierz, K. H. Hofmann, K. Keimel, J. D. Lawson, M. Mislove and D. S. Scott, Continuous
     Lattices and Domains, Encyclopedia of Mathematics and its Applications 93, Cambridge
     University Press, Cambridge, 2003.

 [5] J. Goubault-Larrecq, QRB-domains and the probabilistic powerdomain, Log. Methods Com-
     put. Sci. 8 (2012), no. 1, article 14, 1–32.

 [6] J. Goubault-Larrecq, Probabilistic powerdomains and quasi-continuous domains, Topology
     Proc. 60 (2022), 1–16.

 [7] J. Goubault-Larrecq and A. Jung, QRB, QFS, and the probabilistic powerdomain, Electron.
     Notes Theor. Comput. Sci. 308 (2014), 167–182.

 [8] X. Jia, A. Jung, H. Kou, Q. Li and H. Zhao, All Cartesian closed categories of quasicontinuous
     domains consist of domains, Theoret. Comput. Sci. 594 (2015), 143–150.

 [9] C. Jones, Probabilistic Non-determinism, Ph.D. thesis, University of Edinburgh, 1990.

[10] C. Jones and G. D. Plotkin, A probabilistic powerdomain of evaluations, in Proceedings of the
     Fourth Annual IEEE Symposium on Logic in Computer Science, IEEE Computer Society
     Press, 1989, pp. 186–195.

[11] A. Jung, Cartesian Closed Categories of Domains, CWI Tract 66, Centrum Wiskunde &
     Informatica, Amsterdam, 1989.


                                                 42


---

[12] A. Jung, The classification of continuous domains, in Proceedings of the Fifth Annual IEEE
     Symposium on Logic in Computer Science, IEEE Computer Society Press, 1990, pp. 35–40.

[13] A. Jung and R. Tix, The troublesome probabilistic powerdomain, Electron. Notes Theor.
     Comput. Sci. 13 (1998), 70–91.

[14] T. Kamae, U. Krengel and G. L. O’Brien, Stochastic inequalities on partially ordered spaces,
     Ann. Probab. 5 (1977), 899–912.

[15] Z. Lyu, H. Kou, The probabilistic powerdomain from a topological viewpoint, Top. Appl.,
     237(2018), 237: 26-36.

[16] G. D. Plotkin, Tω as a universal domain, J. Comput. System Sci. 17 (1978), no. 2, 209–236.

[17] R. T. Rockafellar, Convex Analysis, Princeton Mathematical Series 28, Princeton University
     Press, Princeton, NJ, 1970.

[18] D. S. Scott, Outline of a Mathematical Theory of Computation, Technical Monograph PRG-02,
     Oxford University Computing Laboratory, Oxford, 1970.

[19] D. S. Scott and C. Strachey, Toward a Mathematical Semantics for Computer Languages,
     Technical Monograph PRG-06, Oxford University Computing Laboratory, Oxford, 1971.

[20] D. S. Scott, Continuous lattices, in F. W. Lawvere (ed.), Toposes, Algebraic Geometry and
     Logic, Lecture Notes in Mathematics 274, Springer, Berlin, 1972, pp. 97–136.

[21] D. S. Scott, Data types as lattices, SIAM J. Comput. 5 (1976), no. 3, 522–587.

[22] M. B. Smyth and G. D. Plotkin, The category-theoretic solution of recursive domain equations,
     SIAM J. Comput. 11 (1982), no. 4, 761–783.

[23] V. Strassen, The existence of probability measures with given marginals, Ann. Math. Statist.
     36 (1965), 423–439.

[24] V. A. Ubhaya, Isotone functions, dual cones, and networks, Appl. Math. Lett. 14 (2001),
     463–467.




                                               43


---

