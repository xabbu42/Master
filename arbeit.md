
Introduction
============

Throughout this text, we will only use the modal logik S4 and the logic of proofs LP.

Syntax
======

The language of S4 is given by $A := ⊥ ∣ P ∣ A ∧ A ∣ A ∨ A ∣ A → A ∣
□A ∣ ◇A$.  By using the known definitions for $∧$, $∨$ and $◇$ by
formulas using the remaining syntax, we can reduce that to the minimal
language $A := ⊥ ∣ p ∣ A → A ∣ □A$.

The language of LP consists of terms given by $t := c ∣ x ∣ t ⋅ t ∣ t
+ t ∣\: !t$ and formulas given by $A := ⊥ ∣ P ∣ A → A ∣ t{:}A$.

A Hilbert style system for LP is given by the following Axioms and the
rules modus ponens and axiom necessitation. [@artemov2001 p.8]

* $A0$: Finite set of axiom schemes of classical propositional logic
* $A1$: $t{:}F → F$ (Reflection)
* $A2$: $s{:}(F → G) → (t{:}F → (s·t){:}G)$ (Application)
* $A3$: $t{:}F →\;!t{:}(t{:}F)$ (Proof Checker)
* $A4$: $s{:}F → (s+t){:}F$, $t{:}F → (s+t){:}F$ (Sum)

* $R1$: $F → G, F ⊢ G$ (Modus Ponens)
* $R2$: $A ⊢ c:A$, if $A$ is an axiom $A0-A4$ and $c$ a proof constant
        (Axiom Necessitation)

Gentzen Systems for S4 and LP
=============================

In the following text capital greek letters $Γ$, $Δ$ are used for
multisets of formulas, latin letters $P$, $Q$ for atomic formulas and
latin letters $A$,$B$ for arbitrary formulas. We also use the
following shortforms:

$$□Γ := \{□x ∣ x ∈ Γ\}$$
$$Γ,A := Γ ∪ \{A\}$$
$$Γ,Δ := Γ ∪ Δ$$

Throughout this text, we will work with the G3s calculus from
@troelstra2000 [p287], which also used by in @yu2010. It is important to
use a system with the axioms restricted to atomic rules for the
definition of prehistoric loops as the build-up of a sequent $□A, Γ ⊃
Δ, □A$ can introduce prehistoric relations which would otherwise be
missed ^[TODO find an actual example for that]. This is a
Gentzen-style calculus with the following rules:

\renewcommand{\arraystretch}{3}
\begin{longtable}{cc}

\AXC{$P, Γ ⊃ Δ, P$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$}
\DP

\\

\RightLabel{$(∧ ⊃)$}
\AXC{$A, B, Γ ⊃ Δ$}
\UIC{$A ∧ B, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ ∧)$}
\AXC{$Γ ⊃ Δ, A$}
\AXC{$Γ ⊃ Δ, B$}
\BIC{$Γ ⊃ Δ, A ∧ B$}
\DP

\\

\RightLabel{$(∨ ⊃)$}
\AXC{$A, Γ ⊃ Δ$}
\AXC{$B, Γ ⊃ Δ$}
\BIC{$A ∨ B, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ ∨)$}
\AXC{$Γ ⊃ Δ, A, B$}
\UIC{$Γ ⊃ Δ, A ∨ B$}
\DP

\\

\RightLabel{$(→ ⊃)$}
\AXC{$Γ ⊃ Δ, A$}
\AXC{$B, Γ ⊃ Δ$}
\BIC{$A → B, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ →)$}
\AXC{$A,Γ ⊃ Δ, B$}
\UIC{$Γ ⊃ Δ, A → B$}
\DP

\\

\RightLabel{$(□ ⊃)$}
\AXC{$A, □A, Γ ⊃ Δ$}
\UIC{$□A, Γ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ □)$}
\AXC{$□Γ ⊃ ◇Δ, A$}
\UIC{$Γ', □Γ  ⊃ ◇Δ, Δ', □A$}
\DP

\\

\RightLabel{$(◇ ⊃)$}
\AXC{$A, □Γ ⊃ ◇Δ$}
\UIC{$◇A, Γ', □Γ ⊃ ◇Δ, Δ'$}
\DP

&

\RightLabel{$(⊃ ◇)$}
\AXC{$Γ ⊃ Δ, A, ◇A$}
\UIC{$Γ ⊃ Δ, ◇A$}
\DP

\end{longtable}

Again by using the standard definitions for $∨$, $∧$ and $◇$, we can
reduce and simplify the rules to the following minimal but equivalent
system:

\begin{longtable}{cc}

\AXC{$P,Γ ⊃ Δ,P$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$}
\DP

\\

\RightLabel{$(→ ⊃)$}
\AXC{$Γ ⊃ Δ, A$}
\AXC{$B, Γ ⊃ Δ$}
\BIC{$A → B, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ →)$}
\AXC{$A,Γ ⊃ Δ, B$}
\UIC{$Γ ⊃ Δ, A → B$}
\DP

\\

\RightLabel{$(□ ⊃)$}
\AXC{$Γ, A, □A ⊃ Δ$}
\UIC{$Γ, □A ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ □)$}
\AXC{$□Γ ⊃ A$}
\UIC{$Γ', □Γ  ⊃ □A, Δ$}
\DP

\end{longtable}

In @artemov2001 [p.14], a Gentzen-Style system LPG is introduced for
the logic of proofs LP using explicit contraction and weakening
rules, i.e. based on G1c as defined in @troelstra2000 [p.61]. As our
used system for S4 G3s is based on G3c instead, we use a variant G3lp
also based on G3s and therefore directly comparable to G3s. This
variant resembles closely the LPG0 + "lifting rule" system from
@yu2010.

\renewcommand{\arraystretch}{3}
\begin{longtable}{cc}

\AXC{$P, Γ ⊃ Δ, P$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$}
\DP

\\

\RightLabel{$(→ ⊃)$}
\AXC{$Γ ⊃ Δ, A$}
\AXC{$B, Γ ⊃ Δ$}
\BIC{$A → B, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ →)$}
\AXC{$A, Γ ⊃ Δ, B$}
\UIC{$Γ ⊃ Δ, A → B$}
\DP

\\

\RightLabel{$({:} ⊃)$}
\AXC{$A, t{:}A, Γ ⊃ Δ$}
\UIC{$t{:}A, Γ ⊃ Δ$}
\DP

&

\pbox{8cm}{
\RightLabel{$(⊃ :)_t$}
\AXC{$t_1{:}A_1, ..., t_n{:}A_n ⊃ A$}
\UIC{$Γ, t_1{:}A_1, ..., t_n{:}A_n ⊃ t{:}A, Δ$}
\DP
\newline
for any $t$ where $t_1{:}A_1, ..., t_n{:}A_n ⊢_{LP} t{:}A$.
}

\end{longtable}



TODO: proof correct/complete of this system. better display of last rule

In all this rules, arbitrary formulas which occur in the premises and
the conclusion (denoted by repeated multisets $Γ$, $□Γ$, $Δ$ and $◇Δ$)
are called side formulas. Arbitrary formulas which only occur in the
conclusion (denoted by new multisets $Γ$, $Δ$, $Γ'$, $Δ'$) are called
weakening formulas.[^weak] The remaining single new formula in the conclusion
is called the principal formula of the rule. The remaining formulas in
the premises are called active formulas. Active formulas are always
used as subformulas of the principal formula.

[^weak]: Notice that weakening formulas only occur in axioms and the rules $(⊃
□)$, $(◇ ⊃)$, which are also the only rules which restrict the
possible side formulas.

We relate the symbol occurrences in a proof as follows:

* Every occurrence in a side formula of the conclusion corresponds to
  the same occurrence of that symbol in the same side formula in all the
  premises.

* Every occurrence in an active formula of a premise corresponds to
  the same occurrence of that symbol in the corrsponding subformula in
  the principal formula of the rule.

Every symbol occurrence in a premise corresponds to exactly one
symbol occurrence in the conclusion. Therefore all symbol occurrences
in a proof can be divided in disjunct corresponding families of symbol
occurrences. For every such familiy there is exactly one occurrence in
the root sequent of the proof. For us the occurrences of the symbol
$□$ are of special importance.

Formally, a gentzen style proof is denoted by $𝒯 = (T, R)$, where $T
:= {s_0, ..., s_n}$ is the set of occurrences of sequents, and $R :=
\{(s_i,s_j) ∈ T × T ∣ \text{$s_i$ is the conclusion of a rule which
has $s_j$ as a premise}\}$. The only root sequent of $𝒯$ is denoted by
$s_r$. A leaf sequent $s$ is a sequent without any premises, i.e $∀ s'
∈ T s \not R s'$ ^[TODO typeset that correctly].  The relation $R$ is
the inverse of the the parent function $P := \{(s_j, s_i) ∈ T × T ∣
s_i R s_j\}$ defined on $T ∖ \{s_r\}$.

A path in the proof is a list of related sequents $s_r R s_n R ... R
s_0$ starting from the root sequent $s_r$ and ending in a leaf sequent
$s_0$. The path is fully defined by the leaf sequent $s_0$. So we
will use path $s_0$ to mean the full and unique path $s_r R s_n R ... R s_0$ from
the root $s_r$ to the leaf $s_0$. $T↾s$ denotes the subtree of $T$ with root
$s$. The transitive closure of $R$ is denoted by $R^+$ and the
reflexive-transitive closure is denoted by $R^*$.

Annotated S4 Formulas and Proofs
================================

\Begin{definition}[polarity]
We assign a *positive* or *negative polarity* relativ to $A$ to all
subformulas occurrences $B$ in $A$ as follows:

* The only occurrence of $A$ in $A$ has positive polarity.

* If an occurrence $B → C$ in $A$ already has a polarity, then the
  corresponding occurrence of $C$ in $B → C$ has the same polarity and
  the corresponding occurrence of $B$ in $B → C$ has the opposite
  polarity.

* If an occurrence $□B$  already has a polarity, then the corresponding
  occurrence of $B$ in $□B$ has the same polarity.

Similarly all occurrences of subformulas in a sequent $Γ ⊃ Δ$ get
assigned a *polarity* as follows:

* An occurrence of a subformula $B$ in a formula $A$ in $Γ$ has the
  opposite polarity relativ to the sequent $Γ ⊃ Δ$ as the same
  occurance $B$ in the formula $A$ has relativ to $A$.

* An occurrence of a subformula $B$ in a formula $A$ in $Δ$ has the
  same polarity relativ to the sequent $Γ ⊃ Δ$ as the same
  occurance $B$ in the formula $A$ has relativ to $A$.

\End{definition}

This gives the subformulas of a sequent $Γ ⊃ Δ$ the same polarity as
they would have in the equivalent formula $⋀Γ → ⋁Δ$.^[TODO explain
used syntax and equivalence or remove]

The rules of S4 respect the polarities of the subformulas, so that all
corresponding occurrances of subformulas have the same polarity
throughout the proof. We therefore assign positive polarity to
families of positive occurrances and negativ polarity to families of
negative occurrances. Moreover, positive families in a S4 proof which
have occurances introduced by a $(⊃ □)$ rule are called prinicipal
positive families or simply principal families. The remaining
positive families are called non-principal positive families. [^essential]

[^essential]: This is the same terminology as used in @yu2010. In many texts
principal families are also called essential families [for example
@artemov2001].

Given a S4 proof $T$ we annotate the formulas $A$ in the proof in the
following way:

Enumerate all principal positive families as $p_0, ... ,
p_n$, all non-principal positive families as $o_0, ..., o_m$ and all
negative families as $n_0, ..., n_k$.

Define $an_T(A)$ recursively on all occurrences of subformulas $A$ in a
proof $T$ as follows:

* If $A$ is the occurrence of an atomic formula $P$ or $⊥$, then
  $an_T(A) := A$.

* If $A = A_0 → A_1$, then $an_T(A) := an_T(A_0) → an_T(A_1)$

* If $A = □A_0$ and the $□$ belongs to a principal positive family $p_i$, then $an_T(A) := ⊞_i an_T(A_0)$.

* If $A = □A_0$ and the $□$ belongs to a non-principal positive family
  $o_i$, then $an_T(A) := ⊡_i an_T(A_0)$.

* If $A = □A_0$ and the $□$ belongs to a negative family $n_i$, then $an_T(A) := ⊟_i
  an_T(A_0)$.

Similarly we define annotated formulas without the context of a proof
tree by distinguishing all $□$ occurances as seperate families and
droping the distinction between principal positive and non-principal
positive. This leads to the following definition:

Define $an_A(B)$ recursively on all occurrences of subformulas $B$ in a
formula $A$ as follows:

* If $B$ is the occurrence of an atomic formula $P$ or $⊥$, then
  $an_A(B) := B$.

* If $B = B_0 → B_1$, then $an_A(B) := an_A(B_0) → an_A(B_1)$

* If $B = □B_0$ and has positive polarity in $A$, then $an_A(B) := ⊞_i
  an_A(B_0)$ for a new $⊞_i$.

* If $B = □B_0$ and has negative polarity in $A$, then $an_A(B) := ⊟_i
  an_A(B_0)$ for a new $⊟_i$.


So for example the annoteded version of $□((R → □R) → ⊥) → ⊥$ is
$⊟_0((R → ⊞_0 R) → ⊥) → ⊥$


Realization of S4 in LP
=======================

\Begin{definition}[realization function]
A *realization function* $r_A$ for a formula $A$ is a mapping from the
set of different $□$ symbols used in $an_A(A)$ to arbitrary LP terms.
Similarly a *realization function* $r_T$ for a proof $T$ is a mapping
from the set of different $□$ symbols used in $an_T(T)$ to arbitrary
LP terms.
\End{definition}

\Begin{definition}[LP-realization]
By an *LP-realization* of a modal formula $A$ we mean an assignment of
proof polynomials to all occurrences of the modality in $A$ along with
a constant specification of all constants occurring in those proof
polynomials. By $A^r$ we understand the image of $A$ under a
realization $r$ [@artemov2001, 25].
\End{definition}

A LP-realization of $A$ is fully determined by a realization function
$r_A$ and a constant specification of all constants occuring in $r_A$
with $A^r := r_A(an_A(A))$.

\Begin{definition}[normal]
A realization function is *normal* if all symbols for negative families
and non-principal positive families are mapped to distinct
proof variables. A LP-realization is *normal* if the corresponding
realization function is normal and the $CS$ is injective.
\End{definition}

\Begin{theorem}[Realization]
If $S4 ⊢ A$ then $LP ⊢ A^r$ for some normal
LP-realization $r$.
\End{theorem}

\Begin{proof}
Because of $S4 ⊢ A$ and the completeness of G3s, there
exists a G3s proof $𝒯 = (T, R)$ of $⊃ A$.

For all principal families $⊞_i$ in $an_T(T)$, enumerate the
$(⊃ □)$ rules principally introducing an occurrance of $⊞_i$ as
$R_{i,0}, ... R_{i,l_i}$.  We will use $I_{i,0}, ... I_{i,l_i}$ to
denote the premises and $O_{i,0}, ... O_{i,l_i}$ to denote the
conclusions of this rules (so for all $i ≤ n$, $j ≤ l_i$ we have
$I_{i,j}RO_{i,j}$). In total there are $N = Σ_{i = 0}^{n}l_i$ $(⊃
□)$ rules in the proof $T$.

We choose an order $ε(i,j) → \{1, ..., N\}$ of all the $(⊃
□)$ rules such that $ε(i_2,j_2) < ε(i_1,j_1)$ whenever
$O_{i_1,j_1}R^+O_{i_2,j_2}$ (i.e. rules closer to the root $s_r$ are
later in this order).

We define the normal realization function $r_T^0$ by $r_T^0(⊞_i) :=
u_{i,0} + ... + u_{i,l_i}$ and the injective constant specification
$CS^0 := ∅$. The rules of the minimal Gentzen systems G3s for S4 all have a
direct equivalent in G3lp, so the the proof tree $r_T^0(an_T(T))$ formally is
a G3lp proof tree. However it is not a correct proof as the $(⊃ :)$
rule is used without fullfilling the necessary precondition on the
introduced term $t$.

We therefore define inductively the normal realization functions
$r_T^{ε(i,j)}$ and injective constant specifications $CS^{ε(i,j)}$
such that $r_T^{ε(i,j)}(an_T(T↾O_{i_0,j_0}))$ is a correct G3lp proof
based on $CS^{ε(i,j)}$ for all $(i_0,j_0)$ such that $ε(i_0,j_0) ≤ ε(i,j)$.

The rule $R_{i,j}$ has the following annotated form:

\begin{center}
\AXC{$⊟_{k_0} B_{k_0}, ..., ⊟_{k_q} B_{k_q} ⊃ A$}
\UIC{$Γ', ⊟_{k_0} B_{k_0}, ..., ⊟_{k_q} B_{k_q} ⊃ ⊞_i A$}
\DP
\end{center}

By the induction hypothesis there exists an injective constant
specification $CS^{ε(i,j) - 1}$ and a normal realization function
$r_T^{ε(i,j) - 1}$ such that $r_T^{ε(i,j) - 1}(an_T(T↾O_{i0,j0}))$ is
a correct G3lp proof based on $CS^{ε(i,j) - 1}$ for all $(i_0,j_0)$ such that
$ε(i_0,j_0) ≤ ε(i,j) - 1$. From this it follows by a trivial induction
on the proof tree that $r_T^{ε(i,j) - 1}(an_T(T ↾ I_{i,j}))$ is also a
correct G3lp proof. By the correctness of G3lp we therefore have:

\begin{equation}
LP(CS^{ε(i,j) - 1}) ⊢ r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0} ∧ ... ∧ ⊟_{k_q} B_{k_q} → A)
\end{equation}

By the lifting lemma we get a new proof term $t_{i,j}(x_{k_0}, ...,
x_{k_q})$ and a new injective $CS'^{ε(i,j)} ⊃ CS^{ε(i,j) - 1}$ such
that:

\begin{equation}
LP(CS'^{ε(i,j)}) ⊢ r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0} ∧ ... ∧ ⊟_{k_q} B_{k_q}) → t_{i,j}{:}r_T^{ε(i,j) - 1}(A)
\end{equation}

Define $r_T^{ε(i,j)}$ and $CS^{ε(i,j)}$ by replacing $u_{i,j}$ with
$t$ in $r_T^{ε(i,j) - 1}$ and $CS'^{ε(i,j)}$. As $t$ does not contain
any variables $u_{i',j'}$, the formula $r_T^k(⊞_i):A$ will have the
form $(s_0 + ··· +s_{j−1} + t_{i,j} + s_{j+1} + ··· + s_{l_i}){:}A$
for any $k ∈ \{ε(i,j), ..., N\}$. Therefore $LP0 ⊢ t_{i,j}{:}A →
r_T^k(⊞_i){:}A$ follows from repeated use of $A4$. Together with (2)
we get the precondition required for the final $(⊃ :)$ rule in
$r_T^{ε(i,j)}(an_T(T ↾ O_{i,j}))$:

\begin{equation}
LP(CS^{ε(i,j)}) ⊢ r_T^{ε(i,j)}(⊟_{k_0} B_{k_0} ∧ ... ∧ ⊟_{k_q} B_{k_q} ⊃ ⊞_i:A)
\end{equation}

Moreover, this precondition remains fullfilled for the $(⊃ :)$ rule
$R_{i,j}$ in any proof tree $r_T^k(an_T(T))$ for $k > ε(i,j)$.

For the final normal realization function $r_T := r_T^N$ and injective
constant specification $CS := CS^N$ we have that $r_T(an_T(T))$ is a
correct G3lp proof based on $CS$ of $⊃ r_T(A)$. So by correctness of
G3lp we have $LP ⊢ A^r$ for the normal LP-realiziation $r$ given by
$r_T$ and the injective constant specification $CS$.
\End{proof}


Main Proof
==========

Yu proofes in [@yu2010] the following theorem:

\Begin{theorem}[Necessity of Left Prehistoric Loop for Self-referentiality]
If an S4−theorem $A$ has a left-prehistoric-loop-free G3s−proof, then
there is an LP−formula $B$ s.t. $B^◦ = A$ and $⊢_{LP(CS^⊛)} A$
\End{theorem}

Literature
==========

