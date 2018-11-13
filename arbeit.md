
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

A Hilbert style derivation $d$ is sequence of formulas $A_0, ... A_n$
such that any formula is either an axiom A0-A4 or derived from earlier
formulas by a rule R1 or R2. When formulating such derivations, we
will introduce propositional tautologies without derivation and use
the term propositional reasoning for any use of modus ponens together
with a propositional tautology. This is of course correct as axioms A0
together with the modus ponens rule R1 are a complete Hilbert style
system for classical propositional logic. Its easy to see by a simple
complete induction on the proof length that this derivations do
not introduce any new terms not already occurring in the final
propositional tautology.

A constant specification $CS$ is a set of of formulas of the form
$c:A$ with $c$ a proof constant and $A$ an axiom A0-A4. Every LP
derivation naturally generates a finite constant specification of all
formulas derived by axiom necessitation (R2). For a given constant
specification $CS$, $LP(CS)$ is the logic with axiom necessitation
restricted to that $CS$. $LP_0 := LP(∅)$ is the logic without axiom
necessiation.  A constant specification $CS$ is injective, if for each
proof constant $c$, there is at most one formula $c{:}A ∈ CS$.

\Begin{definition}[forgetful projection] \label{proj}
The *forgetful projection* $A˚$ of a LP formula $A$ is the following S4 formula:

* if $A$ is atomic or $⊥$, then $A˚ := A$.
* if $A$ is the formula $A_0 → A_1$ then $A˚ := A_0˚ → A_1˚$
* if $A$ is the formula $t{:}A_0$ then $A˚ := □A_0$

The definition is expanded to sets, multisets and sequents of LP
formulas in the natural way.
\End{definition}

\Begin{lemma}[substitution] \label{subst}
If $Γ ⊢_{LP(CS)} A$ with a derivation $d$, then also $Γ' ⊢_{LP(CS')} A'$
with a derivation $d'$ acquired by replacing all occurrences of a
proof variable $x$ by a proof term $t$ in $Γ$, $CS$ and $d$.
\End{lemma}

\Begin{proof}
Trivial induction over the derivation $d$.
\End{proof}

\Begin{theorem}[deduction theorem] \label{ded}
If $Γ, A ⊢_{LP(CS)} B$, then $Γ ⊢_{LP(CS)} A → B$ [@artemov2001, 9]
\End{theorem}

\Begin{proof}
From a proof $d$ for $A, Γ ⊢_{LP} B$ we inductively construct a proof
$d'$ for $Γ ⊢_{LP} A → B$ as follows:

1\.\ case: $B ≡ A$, then $A → B ≡ A → A$ is a propositional tautology
and derivable from axioms A0 and modus ponens.

2\.\ case: $B$ is an assumption or an axiom A0-A4. Then $d'$ is the
derivation $B$, $B → (A → B)$, $A → B$.

3\.\ case: $B ≡ c:B_0$ is derived by axiom necessitation. Then $d'$ is
the derivation $B_0$, $c{:}B_0$, $c{:}B_0 → (A → c{:}B_0)$, $A → c{:}B_0$.

4\.\ case: $B$ is derived by modus ponens. So there are derivations
$d_l$ and $d_r$ for the premises $C → B$ and $C$. By induction
hypothesis, there are derivations $d_l'$ and $d_r'$ for $A → (C → B)$
and $A → C$. The derivation $d'$ is $(A → (C → B)) → ((A
→ C) → (A → B))$, $d_l'$, $(A → C) → (A → B)$, $d_r'$, $A → B$

\End{proof}

\Begin{corollary} \label{dedvar}
The deduction $d'$ for $Γ ⊢_{LP(CS)} A → B$ only uses variables $x$ also occurring in the
deduction $d$ for $A, Γ ⊢_{LP(CS)} B$.
\End{corollary}

\Begin{proof}
As constructed in the main proof, the new deduction $d'$ only uses
subformulas of $d$ and does not introduce any new terms.
\End{proof}

\Begin{theorem}[lifting lemma] \label{lift}
If $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP} B$, then there is a term $t$
s.t. $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP} t{:}B$. [@artemov2001, 9]
\End{theorem}

\Begin{proof}
From a proof $d$ for $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP} B$
we inductively construct a term $t$ and a proof
$d'$ for $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP} t(x_1,···,x_n){:}B$
as follows:

1\.\ case: $B ≡ x_i{:}A_i$ is an assumption. Then $t := !x_i$ and
$d'$ is the derivation $x_i{:}A_i$, $x_i{:}A_i → !x_i{:}x_i{:}A_i$.

2\.\ case: $B$ is an axiom A0-A4. Then $t := c$ for a new constant
$c$ and $d'$ is the derivation $B$, $c{:}B$.

3\.\ case: $B ≡ c{:}B_0$ is derived by axiom necessitation. Then $t := !c$
and $d'$ is the derivation $B_0$, $c{:}B_0$, $c{:}B_0 → !c{:}c{:}B_0$,
$!c{:}c{:}B_0$ as $B_0$ is an axiom.

4\.\ case: $B$ is derived by modus ponens. So there are derivations
$d_l$ and $d_r$ for the premises $C → B$ and $C$. By induction
hypothesis, there are terms $t_l$ and $t_r$ and derivations $d_l'$ and
$d_r'$ for $t_l{:}(C → B)$ and $t_r{:}C$. Set $t := t_l⋅t_r$ and the
derivation $d'$ is $t_l{:}(C → B) → (t_r{:}C → t_l⋅t_r{:}B)$, $d_l'$,
$t_r{:}C → t_l⋅t_r{:}B$, $d_r'$, $t_l⋅t_r{:}B$

\End{proof}

\Begin{corollary} \label{liftcs}
If $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP(CS)} B$ based on an injective
constant specification $CS$, then there is a term $t$ and a injective
constant specification $CS' ⊃ CS$ s.t. $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP(CS')}
t{:}B$.
\End{corollary}

\Begin{proof}
The proof is exactly the same as for the main theorem, except in the
4. case. In that case we just have to reuse a constant $c ∈ CS$ for
the exact same axiom, if it already exists or else we add the new
constant $c ∉ CS$ to the new constant specification $CS'$.
\End{proof}

\Begin{corollary} \label{liftvar}
The deduction $d'$ for $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP(CS')}
t(x_1,···,x_n){:}B$ and the constant specification of the new
constants $CS' ∖ CS$ only uses variables $x$ also occurring in the
deduction $d$ for $x_1{:}A_1,···,x_n{:}A_n ⊢_{LP} B$.
\End{corollary}

\Begin{proof}
As constructed in the main proof, the new deduction $d'$ only uses
true subformulas and variables already occuring in $d$. Moreover it only
introduces new constants $c$ for axioms $A$ occuring in $d$. Therefore
no new variables are introduced in $d'$ or $CS'$.
\End{proof}


Gentzen System for S4
=====================

In the following text capital greek letters $Γ$, $Δ$ are used for
multisets of formulas, latin letters $P$, $Q$ for atomic formulas and
latin letters $A$,$B$ for arbitrary formulas. We also use the
following shortforms:

$$□Γ := \{□x ∣ x ∈ Γ\}$$
$$Γ,A := Γ ∪ \{A\}$$
$$Γ,Δ := Γ ∪ Δ$$

Throughout this text, we will work with the G3s calculus from
@troelstra2000 [p287], which also used by in @yu2010. It is important to
use a system with the axioms restricted to atomic formulas for the
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
\AXC{$A, □A, Γ ⊃ Δ$}
\UIC{$□A, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ □)$}
\AXC{$□Γ ⊃ A$}
\UIC{$Γ', □Γ  ⊃ □A, Δ$}
\DP

\end{longtable}

In @artemov2001 [p.14], a Gentzen-Style system LPG is introduced for
the logic of proofs LP using explicit contraction and weakening rules,
i.e. based on G1c as defined in @troelstra2000 [p.61]. Later we will follow
@pulver2010 instead and use G3lp with the structural rules absorbed,
but with the classical rules reduced to the same minimal subset as above.

For now the following system closely resembling the only hinted at
"$LPG_0$ + Lifting Lemma Rule" system from @yu2010 is actually the
most practical for our purpose. The reason for this is that it exactly
mirrors the rules of G3s. Other than $LPG_0$ from @yu2010 and
the original Gentzen style systems from @artemov2001 [p.14], it does
not actually deconstruct proof terms but falls back on the Hilbert
style definition of $LP$ to introduce proof terms already fully
constructed. We will call this system G3lift to differentate it from
the later used system G3lp.

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

\RightLabel{$(lift)$}
\AXC{$t_1{:}B_1, ..., t_n{:}B_n ⊃ A$}
\UIC{$t_1{:}B_1, ..., t_n{:}B_n, Γ ⊃ Δ, t{:}A$}
\DP

\\[-3ex]

&

where $t_1{:}B_1, ..., t_n{:}B_n ⊢_{LP} t{:}C$
\end{longtable}

In all this rules, arbitrary formulas which occur in the premises and
the conclusion (denoted by repeated multisets $Γ$, $□Γ$, $Δ$ and $◇Δ$)
are called side formulas. Arbitrary formulas which only occur in the
conclusion (denoted by new multisets $Γ$, $Δ$, $Γ'$, $Δ'$) are called
weakening formulas.[^weak] The remaining single new formula in the conclusion
is called the principal formula of the rule. The remaining formulas in
the premises are called active formulas. Active formulas are always
used as subformulas of the principal formula.

[^weak]: Notice that weakening formulas only occur in axioms and the rules $(⊃
□)$, $(◇ ⊃)$ and $(⊃ :)$, which are also the only rules which restrict the
possible side formulas.

Formally, a gentzen style proof is denoted by $𝒯 = (T, R)$, where $T
:= {s_0, ..., s_n}$ is the set of occurrences of sequents, and $R :=
\{(s_i,s_j) ∈ T × T ∣ \text{$s_i$ is the conclusion of a rule which
has $s_j$ as a premise}\}$. The only root sequent of $𝒯$ is denoted by
$s_r$. A leaf sequent $s$ is a sequent without any premises, i.e $s
\slashed{R} s'$ for all $s' ∈ T$. The relation $R$ is the inverse of
the the parent function $P := \{(s_j, s_i) ∈ T × T ∣ s_i R s_j\}$
defined on $T ∖ \{s_r\}$.

A path in the proof is a list of related sequents $s_r R s_n R ... R
s_0$ starting from the root sequent $s_r$ and ending in a leaf sequent
$s_0$. The path is fully defined by the leaf sequent $s_0$. So we
will use path $s_0$ to mean the full and unique path $s_r R s_n R ... R s_0$ from
the root $s_r$ to the leaf $s_0$. $T↾s$ denotes the subtree of $T$ with root
$s$. The transitive closure of $R$ is denoted by $R^+$ and the
reflexive-transitive closure is denoted by $R^*$.

\Begin{definition}[correspondance]
We relate the subformula (symbol) occurrences in a proof as follows:

* Every subformula (symbol) occurrance in a side formula of a premise
  corresponds to the same occurrence of that subformula (symbol) in
  the same side formula in the conclusion.

* Every active formula of a premise correspond to the topmost
  subformula occurrance of the same formula in the principal formula
  of the conclusion.

* Every subformula (symbol) occurrence in an active formula of a
  premise corresponds to the same occurrence of that subformula
  (symbol) in the corrsponding subformula in the principal formula of
  the rule.

\End{definition}

Every subformula (symbol) occurrence in a premise corresponds to
exactly one subformula (symbol) occurrence in the
conclusion. Therefore all subformula (symbol) occurrences in a proof
can be divided in disjunct corresponding families of symbol
occurrences. For every such familiy there is exactly one occurrence in
the root sequent of the proof.

\Begin{definition}[G3lift preproof]
A *G3lift preproof* is a proof tree using the rules of $G3lift, but where
the $(lift)$ rule may be used without fullfilling the necessary
precondition on the introduced term $t$.
\End{definition}

\Begin{theorem}[subformula property] \label{sub}
Any subformula (symbol) occurrance in a partial Gentzen style
(pre-)proof $T↾s$ in the systems G3lift and G3s corresponds to *at least
one* subformula (symbol) occurrance of the root sequent $s$ of $T↾s$.

Any subformula (symbol) occurrance in a complete Gentzen style
(pre-)proof $T$ in the systems G3lift and G3s correpsonds to *exactly*
one subformula (symbol) occurrance in the root sequent $s_r$ of $T$.
\End{theorem}

\Begin{proof}
TODO
\End{proof}

G3lift is sound and complete
============================

We will show in this section that G3lift is adequate by showing it is equivalent to the
Hilbert system LP from @artemov2001 as introduced in section \ref{syntax}.

\Begin{theorem} \label{equiv1}
$G3lift ⊢ Γ ⊃ Δ ⇒ Γ ⊢_{LP} ⋁Δ$
\End{theorem}

\Begin{proof}
We construct a LP derivation $d$ of $⋁Δ$ by structural induction over
the proof tree $𝒯 = (T, R)$ for $Γ ⊃ Δ$.

1\.\ case: $Γ ⊃ Δ ≡ P, Γ' ⊃ Δ', P$ is an axiom. Then $P$, $P
→ ⋁Δ' ∨ P$, $⋁Δ' ∨ P ≡ ⋁Δ$ is the required LP derivation.
^[TODO usage of $≡$ for sequents here and following cases is confusing]

2\.\ case: $Γ ⊃ Δ ≡ ⊥, Γ' ⊃ Δ$ is an axiom. Then $⊥$, $⊥ → ⋁Δ$, $⋁Δ$ is
the required LP derivation.

3\.\ case: $Γ ⊃ Δ ≡ A → B, Γ' ⊃ Δ$ is derived by a $(→ ⊃)$ rule. So the
premises are $Γ' ⊃ Δ, A$ and $B, Γ' ⊃ Δ$. By the induction hypothesis
there exists LP derivations $d_L$ and $d_R$ for $Γ' ⊢_{LP} ⋁Δ ∨ A$ and
$B, Γ' ⊢_{LP} ⋁Δ$. By the deduction theorem \ref{ded} there exists a LP
derivation $d_R'$ for $Γ' ⊢_{LP} B → ⋁Δ$. Using $d_R'$, the assumption $A → B$
and propositional reasoning, we get $(A → B), Γ' ⊢_{LP} A → ⋁Δ$.
By appending $d_L$ and propositional reasoning we get the final $(A →
B), Γ' ⊢_{LP} ⋁Δ$

4\.\ case: $Γ ⊃ Δ ≡ Γ ⊃ Δ', A → B$ is derived by a $(⊃ →)$ rule. So the
premise is $A, Γ ⊃ Δ', B$. By the induction hypothesis there exists a
LP derivation $d$ for $A, Γ ⊢_{LP} ⋁Δ' ∨ B$. From the deduction
theorem \ref{ded} we get $Γ ⊢_{LP} A → (⋁Δ' ∨ B)$. By propositional reasoning we
get the final $Γ ⊢_{LP} ⋁Δ' ∨ (A → B) ≡ Γ ⊢_{LP} ⋁Δ$.

5\.\ case: $Γ ⊃ Δ ≡ t{:}A, Γ' ⊃ Δ$ is derived by a $(: ⊃)$ rule. So the
premise is $A, t{:}A, Γ' ⊃ Δ$. By the induction hypothesis there
exists a LP derivation $d$ for $A, t{:}A, Γ' ⊢_{LP} ⋁Δ$. By adding
$t{:}A, t{:}A → A, A$ to the beginning of $d$ we get the necessary
derivation $d'$ for $t{:}A, Γ' ⊢_{LP} ⋁Δ$.

6\.\ case: $Γ ⊃ Δ ≡ t_1{:}A_1, ..., t_n{:}A_n, Γ' ⊃ Δ', t{:}A$ is derived
by a $(lift)$ rule. By the precondition on $t$ there exists a
derivation of $t_1{:}A_1, ..., t_n{:}A_n ⊢_{LP} t{:}A$.

\End{proof}

\Begin{corollary} \label{equiv1var}
The deduction $d$ for $Γ ⊢_{LP} ⋁Δ$ only uses variables $x$ which also
occur in the proof tree $𝒯 = (T, R)$ for $G3lift ⊢ Γ ⊃ Δ$ or any
deduction $d_t$ for $t_1{:}A_1, ..., t_n{:}A_n ⊢_{LP} t{:}A$ used in
case 6.
\End{corollary}

\Begin{proof}
As constructed in the main proof, the deduction $d$ only uses true
subformulas and variables already occuring in $T$. For cases 1 and 2
this is immediate as the given derivations directly use subformulas
from $T$. In cases 3, 4 and 5, the starting derivations do not
introduce new variables by induction hypothesis and the use of the
deduction theorem does not introduce new variables by corollary
\ref{dedvar}. The derivation for case 6 is already included in the
corollary and therefore trivially does not introduce new variables.
\End{proof}

\Begin{lemma}[weakening for G3lift] \label{weak}
$G3lift ⊢ Γ ⊃ Δ ⇒ G3lift ⊢ Γ, Γ' ⊃ Δ, Δ'$
\End{lemma}

\Begin{lemma}[contraction for G3lift] \label{contr}
$G3lift ⊢ A, A, Γ ⊃ Δ ⇒ G3lift ⊢ A, Γ ⊃ Δ$
$G3lift ⊢ Γ ⊃ Δ, A, A ⇒ G3lift ⊢ Γ ⊃ Δ, A$
\End{lemma}

\Begin{lemma}[inversion of $(: ⊃)$] \label{drop}
$G3lift ⊢ B, t:B, Γ ⊃ Δ ⇔ G3lift ⊢ B, Γ ⊃ Δ$
\End{lemma}

\Begin{proof}
The $(⇐)$ direction is just a weakening (\ref{weak}). The $(⇒)$ direction is shown 
by a structural induction over the proof tree for $B, t{:}B, Γ ⊃ Δ$:

1\.\ case: $t{:}B$ is a weakening formula of an axiom or a $(⊃ :)$
rule. Then leaving out $t{:}B$ keeps the proof intact.

2\.\ case: $t{:}B$ is a side formula of the last rule. By induction hypothesis
the premises of the rules are provable without $t{:}B$. Append the same
rule to get a proof of $B, Γ ⊃ Δ$.

3\.\ case: $t{:}B$ is the principal formula of the last rule, then the premise
is $B, B, t{:}B, Γ ⊃ Δ$. By induction hypothesis we get a proof for
$B, B, Γ ⊃ Δ$ and by contraction (\ref{contr}) we get $B, Γ ⊃ Δ$.

\End{proof}

\Begin{lemma}[inversion of $(⊃ →)$] \label{revers}
$G3lift ⊢ Γ ⊃ Δ, A → B ⇔ G3lift ⊢ A, Γ ⊃ Δ, B$
\End{lemma}

\Begin{proof}
The $(⇐)$ direction is trivial by appending a $(⊃ →)$ rule to the
given proof.  The $(⇒)$ direction is shown by a structural induction
on the proof tree for $Γ ⊃ Δ, A → B$:

1\.\ case: $A → B$ is a weakening formula of an axiom or a $(⊃ :)$
rule. Then weakening in $A$ on the left and $B$ on the right instead
leaves the proof intact.

2\.\ case: $A → B$ is a side formula of the last rule. By induction hypothesis
the premises of the rules are provable with $A → B$ replaced
by $A$ on the left and $B$ on the right. Append the same
rule to get a proof of $A, Γ ⊃ Δ, B$.

3\.\ case: $A → B$ is the principal formula of the last rule, then the premise
is the required $A, Γ ⊃ Δ, B$ and removing the last rule gives the
required proof.
\End{proof}

\Begin{lemma}[cut elemination for G3lift] \label{cut}
If $G3lift ⊢ A, Γ ⊃ Δ$ and $G3lift ⊢ Γ' ⊃ Δ', A$ then $G3lift ⊢ Γ,Γ' ⊃ Δ,Δ'$.
\End{lemma}

\Begin{proof}
By a simultanous structural induction over the proof trees $𝒯_L$ for
$A, Γ ⊃ Δ$, $𝒯_R$ for $Γ' ⊃ Δ', A$ and the build up of $A$ (i.e we
will use the induction hypothesis to cut with the same formulas but
shorter subtrees of the given proof trees as well as to cut different
proof trees with lower rank formulas):

1\.\ case: $A$ is a weakening formula in the last rule of one of the proofs. We get the
required proof for $Γ ⊃ Δ$ by leaving out $A$ from that proof.

2\.\ case: $A$ is a side formula in the last rule of $𝒯_L$. By induction
hypothesis we can cut the premises $A, Γ_i ⊃ Δ_i$ of that rule with
$Γ' ⊃ Δ', A$ to get $Γ_i, Γ' ⊃ Δ_i, Δ'$. Applying the same rule we get
the required proof for $Γ,Γ' ⊃ Δ,Δ'$.

3\.\ case: $A$ is a side formula in the last rule of $𝒯_R$. This case is
handled simetrical to the previous one.

4\.\ case: $A$ is the principal formula in the last rules of $𝒯_L$ and
$𝒯_R$. Then we have the following subcases:

4.1: The last rules are axioms. Then $A$ is atomic and $A ∈ Δ$ and $A
∈ Γ'$ as there is no axiom with a principal $⊥$ on the
right. Therefore also $Γ,Γ' ⊃ Δ,Δ'$ is an axiom.

4.2:  $A$ has the form $A_0 → A_1$. Then the last rules of $𝒯_L$ and
$𝒯_R$ have the following form:

\renewcommand{\arraystretch}{3}
\begin{longtable}{cc}

\RightLabel{$(→ ⊃)$}
\AXC{$Γ ⊃ Δ, A_0$}
\AXC{$A_1, Γ ⊃ Δ$}
\BIC{$A_0 → A_1, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ →)$}
\AXC{$A_0, Γ' ⊃ Δ', A_1$}
\UIC{$Γ' ⊃ Δ', A_0 → A_1$}
\DP
\end{longtable}

By induction hypothesis for the lower rank formulas $A_0$ and $A_1$ we
can cut the single premise $A_0, Γ' ⊃ Δ', A_1$ of the $(⊃ →)$ rule
with both premises of the $(→ ⊃)$ rule to get a proof for $Γ, Γ, Γ',
Γ' ⊃ Δ, Δ, Δ', Δ'$. By contraction (\ref{contr}) we get the required
proof for $Γ, Γ' ⊃ Δ, Δ'$.

4.3:  $A$ has the form $t{:}A_0$. Then the last rules of $𝒯_L$ and
$𝒯_R$ have the following form:

\renewcommand{\arraystretch}{3}
\begin{longtable}{cc}

\RightLabel{$({:} ⊃)$}
\AXC{$A_0, t{:}A_0, Γ ⊃ Δ$}
\UIC{$t{:}A_0, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(lift)$}
\AXC{$t_1{:}B_1, ..., t_n{:}B_n ⊃ A_0$}
\UIC{$Γ'', t_1{:}B_1, ..., t_n{:}B_n ⊃ t{:}A_0, Δ'$}
\DP

\end{longtable}

By lemma \ref{drop}, we have a proof for $A_0, Γ ⊃ Δ$. By the
induction hypothesis for the lower rank formula $A_0$ we can cut that
with the premise $t_1{:}B_1, ..., t_n{:}B_n ⊃ A_0$ to get $Γ, t_1{:}B_1,
..., t_n{:}B_n ⊃ Δ$. By weakening (\ref{weak}) we finally get the
required proof for $Γ, Γ' ⊃ Δ, Δ'$ as $\{t_1{:}B_1, ..., t_n{:}B_n\} ⊆
Γ'$.
\End{proof}

\Begin{lemma} \label{genax}
$G3lift ⊢ A, Γ ⊃ Δ, A$ for any LP formula $A$.
\End{lemma}

\Begin{theorem} \label{equiv2}
$Γ ⊢_{LP} A ⇒ G3lift ⊢ Γ ⊃ A$
\End{theorem}

\Begin{proof}
By complete induction over the length of the derivation $d$ for $Γ ⊢_{LP} A$.

1\.\ case $A$ is an axiom A0. By the completeness of G3c included in
G3lift there exists a derivation of $Γ ⊃ A$ and $⊃ A$ using the subset G3c.

2\.\ case $A$ is an axiom $A1-A4$. As the following derivations show, $⊃
A$ can be derived for each axiom using lemma \ref{genax} for the base
cases. $Γ ⊃ A$ follows from weakening (\ref{weak}).

TODO

3\.\ case $A ∈ Γ$ is an assumption. We get the required proof for $A,
Γ' ⊃ A$ directly from lemma \ref{genax}.

4\.\ case $A ≡ c:B$ is derived by rule R1 (Axiom Necessitation). Then
$B$ is an axiom and there is a G3lift proof for $⊃ B$ by induction
hypothesis. Appending a $(⊃ :)$ rule with $t = c$ gives a G3lift proof
for $Γ ⊃ c:A$.

5\.\ case $A$ is dericed by rule R0 (Modus Ponens). By induction
hypothesis, we have G3lift proofs for $Γ ⊃ B → A$ and $Γ ⊃ B$ for the
premises of the modus ponens rule. By lemma \ref{revers} we get a G3lift
proof for $B, Γ⊃ A$ and by lemma \ref{cut} we get the required proof
for $Γ ⊃ A$.
\End{proof}


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
p_{n_p}$, all non-principal positive families as $o_0, ..., o_{n_o}$ and all
negative families as $n_0, ..., n_{n_n}$.

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
realization function is normal and the $CS$ is injective. ^[TODO
probably shoud not misuse normal here for non-principal positive families]
\End{definition}

\Begin{theorem}[Realization] \label{realization}
If $S4 ⊢ A$ then $LP ⊢ A^r$ for some normal
LP-realization $r$.
\End{theorem}

\Begin{proof}
Because of $S4 ⊢ A$ and the completeness of G3s, there
exists a G3s proof $𝒯 = (T, R)$ of $⊃ A$.

For all principal families $⊞_i$ in $an_T(T)$, enumerate the
$(⊃ □)$ rules principally introducing an occurrance of $⊞_i$ as
$R_{i,0}, ... R_{i,n_i}$.  We will use $I_{i,0}, ... I_{i,n_i}$ to
denote the premises and $O_{i,0}, ... O_{i,n_i}$ to denote the
conclusions of this rules (so for all $i ≤ n$, $j ≤ n_i$ we have
$I_{i,j}RO_{i,j}$). In total there are $N = Σ_{i = 0}^{n}n_i$ $(⊃
□)$ rules in the proof $T$.

We choose an order $ε(i,j) → \{1, ..., N\}$ of all the $(⊃
□)$ rules such that $ε(i_2,j_2) < ε(i_1,j_1)$ whenever
$O_{i_1,j_1}R^+O_{i_2,j_2}$ (i.e. rules closer to the root $s_r$ are
later in this order).

We define the normal realization function $r_T^0$ by $r_T^0(⊞_i) :=
u_{i,0} + ... + u_{i,n_i}$ and the injective constant specification
$CS^0 := ∅$. The rules of the minimal Gentzen systems G3s for S4 all
have a direct equivalent in G3lift, so by a trivial induction the proof
tree $r_T^0(an_T(T))$ is a G3lift preproof. However it is not a G3lift
proof as none of the $(lift)$ rules fullfill the necessary precondition
on the introduced term $t$.

We therefore define inductively the normal realization functions
$r_T^{ε(i,j)}$ and injective constant specifications $CS^{ε(i,j)}$
such that $r_T^{ε(i,j)}(an_T(T↾O_{i_0,j_0}))$ is a correct G3lift proof
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
a correct G3lift proof based on $CS^{ε(i,j) - 1}$ for all $(i_0,j_0)$
such that $ε(i_0,j_0) < ε(i,j)$. From this it follows by a trivial
induction on the proof tree that $r_T^{ε(i,j) - 1}(an_T(T ↾ I_{i,j}))$
is also a correct G3lift proof. By theorem \ref{equiv1} we therefore
have a derivation for:

\begin{equation} \label{start}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q} B_{k_q}) ⊢_{LP(CS^{ε(i,j) - 1})} r_T^{ε(i,j) - 1}(A)
\end{equation}

By the corollary \ref{liftcs} of the lifting lemma, we get a new proof
term $t_{i,j}(x_{k_0}, ..., x_{k_q})$ and a new injective
$CS'^{ε(i,j)} = CS^{ε(i,j) - 1} ∪ \{c_{i,j,0}{:}A_{i,j,0}, ...,
c_{i,j,m_{i,j}}:A_{i,j,m_{i,j}}\}$ such that:

\begin{equation} \label{lifted}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q} B_{k_q}) ⊢_{LP(CS'^{ε(i,j)})} t_{i,j}{:}r_T^{ε(i,j) - 1}(A)
\end{equation}

Define $r_T^{ε(i,j)}$ and $CS^{ε(i,j)}$ by replacing $u_{i,j}$ with
$t$ in $r_T^{ε(i,j) - 1}$ and $CS'^{ε(i,j)}$. By the substitution
lemma \ref{subst}, \ref{lifted} still holds for $r_T^{ε(i,j)}$ and
$CS^{ε(i,j)}$. The formula $r_T^k(⊞_i A)$ has the form $(s_0 + ···
+s_{j−1} + t_{i,j} + s_{j+1} + ··· + s_{n_i}){:}A$. Therefore $LP_0 ⊢
t_{i,j}{:}A → r_T^k(⊞_i){:}A$ follows from repeated use of $A4$
Together with the substituted \ref{lifted} we get the precondition
required for the final $(⊃ :)$ rule in $r_T^{ε(i,j)}(an_T(T ↾
O_{i,j}))$:


\begin{equation} \label{precond}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q}
B_{k_q}) ⊢_{LP(CS^{ε(i,j)})} r_T^{ε(i,j) - 1}(⊞_i A)
\end{equation}

Moreover, this precondition remains fullfilled for the $(⊃ :)$ rule
$R_{i,j}$ in any proof tree $r_T^k(an_T(T))$ for $k > ε(i,j)$ again by
the substitution lemma \ref{subst}.

For the final normal realization function $r_T^N$ and injective
constant specification $CS^N$ we have that $r_T^N(an_T(T))$ is a
correct G3lift proof based on $CS^N$ of $⊃ r_T(A)$. So by theorem
\ref{equiv1} of G3lift we have $LP ⊢ A^r$ for the normal LP-realiziation
$r$ given by $r_T^N$ and the injective constant specification $CS^N$.
\End{proof}

\Begin{corollary} \label{realvar}
There exist derivations $d^k_{i,j}$ for the precondition
\ref{precond} of all rules $R_{i,j}$ in $r_T^k(an_T(T))$ and for any
$k ≥ ε(i,j)$, which do not introduce new variables.
\End{corollary}

\Begin{proof}
Proof by complete induction over the order $ε(i,j)$.

Given a rule $R_{i,j}$, there exist derivations $d^k_{i0,j0}$
which do not introduce new variables for the precondition of any rule
$R_{i_0,j_0}$ in $r_T^k(an_T(T ↾ I_{i,j}))$ as $ε(i_0,j_0)
< ε(i,j) ≤ k$ for all this rules. Using the exact same steps as in the
main proof but using the realization function $r_T^k$, we get a
derivation $d$ for \ref{start} which does not introduce new variables
by the corollary \ref{equiv1var}, a derivation $d'$ for \ref{lifted}
which does not introduce new variables by the corollary \ref{liftvar}
and finally a derivation $d^k_{i,j}$ for \ref{precond} which also does
not introduce new variables.^[TODO possibly clearer by using
$d^{ε(i,j)}_{i0,j0}$] and substitution lemma]
\End{proof}

Prehistoric Phenomena
=====================

\Begin{definition}[History]
In branch $s$ of the form $s_rR^*O_{i,j}RI_{i,j}R^*s$ in a
G3s−proof $T$, the path $s_rR^*O_{i,j}$ is called a *history* of $p_i$
in branch $s$. The remaining sequents $I_{i,j}R^*s$ is called a
*pre-history* of $p_i$ in branch $s$. ^[vgl. @yu2010, 389]
\End{definition}

\Begin{definition}[Prehistoric Relation]
For any principal positive families $p_i$ and $p_h$ and any branch $s$ of
the form $s_rR^*O_{i,j}RI_{i,j}R∗s$ in a S4 proof $𝒯 = (T, R)$:

(1) If $an_T(I_{i,j})$ has the form $⊟_{k_0}B_{k_0}, ...,
⊟_{k}B_{k_q}(⊞_h:C)), ..., ⊟_{k_q}B_{k_q} ⊃ A$, then $p_h$ is a *left
prehistoric family* of $p_i$ in $s$ with notation $h ≺^s_L i$.

(2) If $an_T(I_{i,j})$ has the form $⊟_{k_0} B_{k_0} ∧ ... ∧
⊟_{k_q}B_{k_q} ⊃ A(⊞_h:C)$ then $p_h$ is a *right prehistoric family*
of $p_i$ in $s$ with notation $h ≺^s_R i$.

(3) The relation of *prehistoric family* in $s$ is defined by: $≺^s := ≺^s_L ∪ ≺^s_R$.
The relation of *(left, right) prehistoric family* in $T$ is defined by:
$≺_L := ⋃\{≺^s_L |\text{$s$ is a leaf}\}$, $≺_R := ⋃\{≺^s_R |\text{$s$
is a leaf}\}$ and $≺ := ≺_L ∪ ≺_R$.

\End{definition}

The following lemma provides the connection between these two definitions:

\Begin{lemma} \label{prehist}
There is an occurrence of $⊞_h$ in a pre-history of $p_i$ in the branch
$s$ iff $h ≺^s i$.
\End{lemma}

\Begin{proof}
(⇒): $⊞_h$ occurres in a sequent $s'$ in a pre-history of $p_i$ in the
path $s$, so the path $s$ has the form
$s_rR^*O_{i,j}RI_{i,j}R^*s'R^*s$ for some $j ≤ n_i$. By the subformula
theorem \ref{sub}, there is an occurrance of $⊞_h$ in $I_{i,j}$ as
$s'$ is part of $T↾I_{i,j}$. If this occurrance is on the left we have
$h ≺^s_L i$, if it is on right we have $h ≺^s_R i$. In both cases $h
≺^s i$ holds.

(⇐): By definition there is a $I_{i,j}$ in $s$, where $⊞_h$ occurres
either on the left (for $h ≺^s_L i$) or on the right (for $h ≺^s_R
i$). $I_{i,j}$ is part of the pre-history of $R_{i,j}$ in $s$.
\End{proof}

TODO: paraphrase some of the remarks from @yu2010.

\Begin{lemma} \label{noref}
For any principal positive family $p_i$, $i \nprec_R i$.
\End{lemma}

\Begin{proof}
Assume for a contradiction that $i ≺_R i$. It follows from the
definition of $≺_R$, that there is a rule $R_{i,j}$ with $⊞_iA(⊞_iB)$
as the principal formula. By the subformula property \ref{sub}
$⊞_iA(⊞_iB)$ corresponds to a subformula in the root sequent. Also by
the subformula property there is only one occurrance of $⊞_i$ in the
root sequent.
\End{proof}

\Begin{lemma} \label{trans}
If $k ≺_R j$ and $j ▹ i$, then $k ▹ i$, where $▹$ is any one of $≺$, $≺_L$, $≺_R$, $≺^s$ , $≺^s_L$ or $≺^s_R$.
\End{lemma}

\Begin{proof}
Since $k ≺_R j$, there is a $⊞_k$ occurring in the scope of a
principally introduced $⊞_j$. All corresponding occurrances of $⊞_j$
are part of corresponding occurrances of the subformula $⊞_jA(⊞_kB)$,
with exactly one occurrance in the root sequent $s_r$ by the
subformula property \ref{sub}. So wherever $⊞_j$ occurs in the proof
$T$, there is a $⊞_k$ occurring in the scope of it.

For any $▹$, we have $j ▹ i$ because some occurrance of $⊞_j$ in a
subformula of the premise of a rule $R_{i,q}$. By the previous
statement there is also an occurrance of $⊞_k$ in the same scope, and
therefore also $k ▹ i$.
\End{proof}

\Begin{definition}[Prehistoric Loop]
In a G3s−proof $T$, the ordered list of principal positive families
$p_{i_0},..., p_{i_{n-1}}$ with length $n$ is called a *prehistoric loop* or *left
prehistoric loop* respectively, if we have: $i_0 ≺ i_2 ≺ ... ≺ i_{n-1} ≺
i_0$ or $i_0 ≺_L i_2 ≺_L ... ≺_L i_{n-1} ≺_L i_0$.
\End{definition}

\Begin{theorem}
$T$ has a prehistoric loop iff $T$ has a left prehistoric loop.
\End{theorem}

\Begin{proof}
The (⇐) direction is trivial. The (⇒) direction is proven by complete
induction on the length of the loop as follow:

$n = 1$: $i_0 ≺ i_0$ so either $i_0 ≺_R i_0$ or $i_0 ≺_L i_0$. As $i_0
≺_R i_0$ is impossible by lemma \ref{noref}, we have $i_0 ≺_L i_0$ and the
loop already is a left prehistoric loop.

$n - 1 ⇒ n$: If $i_k ≺_L i_{k+1 \mod n}$ for all $k < n$, then the
loop already is a left prehistoric loop and we are finished. Otherwise
there is a $k < n$ such that $i_k ≺_R i_{k+1 \mod n} ≺ i_{k+2 \mod
n}$. By lemma \ref{trans} we also have $i_k ≺ i_{k+2 \mod n}$ and
therefore the sublist of length $n - 1$ without $i_{k+1 \mod n}$ is
also a prehistoric loop. By the induction hypothesis, $T$ has a left
prehistoric loop.
\End{proof}


Main Proof
==========

\Begin{lemma} \label{variablefree}
Any provisional variable $u_{x,y}$, which does not occur in
$I^{ε(i,j)−1}_{i,j}$, does not occur in $CS^{ε(i,j)}$.
\End{lemma}

\Begin{proof}
By the subformula property \ref{sub} for G3lift proofs, $u_{x,y}$ does
not occur in $r^{ε(i,j)−1}(an_T(T↾I_{i,j}))$. By the corollary
\ref{equiv1var} using corollary \ref{realvar} for case 6, the
derivation $d_{i,j}$ as constructed in the realization proof does not
contain $u_{x,y}$. By the corollary \ref{liftvar} of the lifting
theorem \ref{lift}, $CS'_{i,j}$ and $t_{i,j}$ do not contain
$u_{x,y}$. So also $CS_{i,j}$ does not contain $u_{x,y}$. ^[TODO check
and better formulation]
\End{proof}

\Begin{lemma} \label{epsilon}
If a G3s−proof $T$ is prehistoric-loop-free, then we can realize it in
such a way that: If $h_2 ≺ h_1$, then $ε(h_2,j_2) < ε(h_1,j_1)$ for any
$j_1 ≤ l_{h_1}$ and $j_2 ≤ m_{h_2}$.
\End{lemma}

\Begin{proof}
For a prehistoric-loop-free proof $T$, $≺$ describes a directed
acyclic graph. Therefore there exists a topological order
$p_{k_0},...,p_{k_{n_p}}$ of the $n_p + 1$ principal positive families
$p_0, ..., p_{n_p}$. For any path $s$ of the form
$s_rR^*O_{i_1,j_1}R^+O_{i_2,j_2}R^*s$, we have $i_2 ≺ i_1$ by lemma
\ref{prehist}. So the order $ε(k_x,j) := Σ_{w = 0}^{x-1}l_{k_w}$
defined for each family $p_{k_x}$ and $j ≤ l_{k_x}$ by handling the
families $p_i$ in the given topological order $k_x$ fullfills the
necessary condition to be used in the realization theorem
\ref{realization} and at the same time the condition given in this
lemma.
\End{proof}

\Begin{lemma} \label{constants}
Assume the proof tree is prehistoric-loop-free. Taken the $ε$ as
defined in lemma \ref{epsilon}, we have: If $ε(i_0,j_0) ≥ ε(i,j)$,
then for any $k_0 ≤ m_{i_0,j_0}$ and any $k ≤ m_{i,j}$,
$c_{i_0,j_0,k_0}$ does not occur in $A^N_{i,j,k}$ for the single
$A^N_{i,j,k}$ such that $c_{i,j,k}{:}A^N_{i,j,k} ∈ CS^N$
\End{lemma}

\Begin{proof}
By the construction in the proof of the realization theorem
\ref{realization}, $d_{i,j}$ is a derivation of $r_T^{ε(i,j) -
1}(an_T(I_{i,j}))$. For any $⊞_h$ occuring in $I_{i,j}$, we have by
definition $h ≺ i$, and therefore by lemma \ref{epsilon} $ε(h,j_h) ≤
ε(i,j)$ for all $j_h ≤ m_h$. So any provisional variable $u_{h,j_h}$
occuring in $r_T^0(an_T(I_{i,j}))$ is already replaced in $r_T^{ε(i,j)
- 1}(an_T(I_{i,j}))$, which is therefore provisional variable free. So
by lemma \ref{variablefree} also $CS^{ε(i,j)}$ is provisional
variable free and $A^N_{i,j,k} ≡ A_{i,j,k}$ for any
$c_{i,j,k}{:}A_{i,j,k}$ introduced in $CS^{ε(i,j)}$. As any
$c_{i_0,j_0,k_0}$ for any $ε(i_0,j_0) ≥ ε(i,j)$ is not yet introduced
in $r_T^{ε(i,j) - 1}(an_T(I_{i,j}))$, it does not occur in $A_{i,j,k}$
and therefor also not in $A^N_{i,j,k} ≡ A_{i,j,k}$
\End{proof}

With this three lemmas we can finally proof the main result of @yu2010
[394]:

\Begin{theorem}[Necessity of Left Prehistoric Loop for Self-referentiality]
If a S4−theorem $A$ has a left-prehistoric-loop-free G3s−proof, then
there is a LP−formula $B$ s.t. $B^◦ = A$ and $⊢_{LP(CS^⊛)} B$
\End{theorem}

\Begin{proof}
Given a left-prehistoric-loop-free G3s−proof $T$ for $A$, use lemma
\ref{epsilon} and the realization theorem \ref{realization} to
construct a realization function $r_T^N$ and a constant specification
$CS^N$ such that $B := r_T^N(an_T(A))$ is a realization of $A$.

Assume for contradiction, that the generated $CS^N$ is
self-referential, i.e. there exist constants
$c_{i_0,j_0,k_0},...,c_{i_{n-1},j_{n-1},k_{n-1}}$ such that for all $x
< n$ the single $c_{i_x,j_x,k_x}{:}A^N_{i_x,j_x,k_x} ∈ CS^N$ contains
the next constant $c_{i_{x'},j_{x'},k_{x'}}$ with $x' := x + 1 \mod
n$. By lemma \ref{constants} we get $ε(i_{x'},j_{x'}) <
ε(i_x,j_x)$ for all $x ≤ n$. So $ε(i_n,j_n) < ... < ε(i_1,j_1) <
ε(i_0,j_0) < ε(i_n,j_n)$, which is impossible. Therefore the generated
$CS^N$ is not self-referential and we have $⊢_{LP(CS^⊛)} B$.
\End{proof}

Literature
==========

