

TODO:

* replace loop with cycle, add explanation and ref to @yu2017
* fix typesetting of cut rules (same as lift)
* consistent numbering and handling of lists (is it worth the noise?)

Introduction
============

Syntax
======

The language of S4 is given by $A := ⊥ ∣ P ∣ A_0 ∧ A_1 ∣ A_0 ∨ A_1 ∣ A_0 → A_1 ∣
□A ∣ ◇A$.  By using the known definitions for $∧$, $∨$ and $◇$ by
formulas using the remaining syntax, we can reduce that to the minimal
language $A := ⊥ ∣ p ∣ A_0 → A_1 ∣ □A$.

The language of LP consists of terms given by $t := c ∣ x ∣ t_0 ⋅ t_1 ∣ t_0
+ t_0 ∣\: !t$ and formulas given by $A := ⊥ ∣ P ∣ A_0 → A_1 ∣ t{:}A$.

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

\Begin{definition}[Constant Specification]
A *constant specification* $CS$ is a set of of formulas of the form
$c:A$ with $c$ a proof constant and $A$ an axiom A0-A4.
\End{definition}

Every LP derivation naturally generates a finite constant
specification of all formulas derived by axiom necessitation (R2). For
a given constant specification $CS$, $LP(CS)$ is the logic with axiom
necessitation restricted to that $CS$. $LP_0 := LP(∅)$ is the logic
without axiom necessitation.  A constant specification $CS$ is
injective, if for each proof constant $c$, there is at most one
formula $c{:}A ∈ CS$.

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
The deduction $d'$ for $Γ ⊢_{LP(CS)} A → B$ only uses variables $x$
also occurring in the deduction $d$ for $A, Γ ⊢_{LP(CS)} B$.
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
true subformulas and variables already occurring in $d$. Moreover it only
introduces new constants $c$ for axioms $A$ occurring in $d$. Therefore
no new variables are introduced in $d'$ or $CS'$.
\End{proof}


Gentzen System for S4
=====================

In the following text capital greek letters $Γ$, $Δ$ are used for
multisets of formulas, latin letters $P$, $Q$ for atomic formulas and
latin letters $A$,$B$ for arbitrary formulas. We also use the
following short forms:

$$□Γ := \{□x ∣ x ∈ Γ\}$$
$$Γ,A := Γ ∪ \{A\}$$
$$Γ,Δ := Γ ∪ Δ$$

Throughout this text, we will use the G3s calculus from @troelstra2000
[p287] for our examples with additional rules $(¬⊃)$ and $(⊃¬)$ as we
are only concerned with classical logic (see figure \ref{G3sfull}).
For proofs on the other hand we will use a minimal subset of that
system using the standard derived definitions for $¬$, $∨$, $∧$ and $◇$ as
given by \ref{G3smin}. All the missing rules from the full system are
admissible in the minimal system using this definitions.

\renewcommand{\arraystretch}{3}
\begin{figure} \caption{Full G3s} \label{G3sfull}
\begin{longtable}{cc}

\AXC{$P, Γ ⊃ Δ, P$ $(Ax)$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$ $(⊥⊃)$}
\DP

\\

\RightLabel{$(¬ ⊃)$}
\AXC{$Γ ⊃ Δ, A$}
\UIC{$¬A, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ ¬)$}
\AXC{$A, Γ ⊃ Δ$}
\UIC{$Γ ⊃ Δ, ¬A$}
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
\end{figure}

\begin{figure} \caption{Minimal G3s} \label{G3smin}
\begin{longtable}{cc}

\AXC{$P,Γ ⊃ Δ,P$ $(Ax)$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$ $(⊥⊃)$}
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
\end{figure}

In @artemov2001 [p.14], a Gentzen-Style system LPG is introduced for
the logic of proofs LP using explicit contraction and weakening rules,
i.e. based on G1c as defined in @troelstra2000 [p.61]. Later we will
follow @pulver2010 instead and use G3lp with the structural rules
absorbed, but with the classical rules reduced to the same minimal
subset as in figure \ref{G3smin}.

For now the system from figure \ref{G3lift} closely resembling the
only hinted at "$LPG_0$ + Lifting Lemma Rule" system from @yu2010 is
actually the most practical for our purpose. The reason for this is
that it exactly mirrors the rules of G3s. Other than $LPG_0$ from
@yu2010 and the original Gentzen style systems from @artemov2001
[p.14], it does not actually deconstruct proof terms but falls back on
the Hilbert style definition of $LP$ to introduce proof terms already
fully constructed. We will call this system G3lift to differentiate it
from the later used system G3lp.

\begin{figure} \caption{G3lift} \label{G3lift}
\begin{longtable}{cc}

\AXC{$P, Γ ⊃ Δ, P$ $(Ax)$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$ $(⊥⊃)$}
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

\RightLabel{(lift)}
\AXC{$t_1{:}B_1, ..., t_n{:}B_n ⊃ A$}
\UIC{$t_1{:}B_1, ..., t_n{:}B_n, Γ ⊃ Δ, t{:}A$}
\DP

\\[-3ex]

&

where $t_1{:}B_1, ..., t_n{:}B_n ⊢_{LP} t{:}C$
\end{longtable}
\end{figure}

In all this rules, arbitrary formulas which occur in the premises and
the conclusion (denoted by repeated multisets $Γ$, $□Γ$, $Δ$ and $◇Δ$)
are called side formulas. Arbitrary formulas which only occur in the
conclusion (denoted by new multisets $Γ$, $Δ$, $Γ'$, $Δ'$) are called
weakening formulas.[^weak] The remaining single new formula in the conclusion
is called the principal formula of the rule. The remaining formulas in
the premises are called active formulas. Active formulas are always
used as subformulas of the principal formula.

[^weak]: Notice that weakening formulas only occur in axioms and the rules $(⊃
□)$, $(◇ ⊃)$ and (lift), which are also the only rules which restrict the
possible side formulas.

Formally, a Gentzen style proof is denoted by $𝒯 = (T, R)$, where $T
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

\Begin{definition}[correspondence] \label{corr}
We relate the subformula (symbol) occurrences in a proof as follows:

* Every subformula (symbol) occurrence in a side formula of a premise
  corresponds to the same occurrence of that subformula (symbol) in
  the same side formula in the conclusion.

* Every active formula of a premise correspond to the topmost
  subformula occurrence of the same formula in the principal formula
  of the conclusion.

* Every subformula (symbol) occurrence in an active formula of a
  premise corresponds to the same occurrence of that subformula
  (symbol) in the corresponding subformula in the principal formula of
  the rule.

\End{definition}

Every subformula (symbol) occurrence in a premise corresponds to
exactly one subformula (symbol) occurrence in the
conclusion. Therefore all subformula (symbol) occurrences in a proof
can be divided in disjoint corresponding families of symbol
occurrences. For every such family there is exactly one occurrence in
the root sequent of the proof.

\Begin{definition}[G3lift preproof]
A *G3lift preproof* is a proof tree using the rules of G3lift, but where
the (lift) rule may be used without fulfilling the necessary
precondition on the introduced term $t$.
\End{definition}

\Begin{theorem}[subformula property] \label{sub}
Any subformula (symbol) occurrence in a partial Gentzen style
(pre-)proof $T↾s$ in the systems G3lift and G3s corresponds to *at least
one* subformula (symbol) occurrence of the root sequent $s$ of $T↾s$.

Any subformula (symbol) occurrence in a complete Gentzen style
(pre-)proof $T$ in the systems G3lift and G3s corresponds to *exactly*
one subformula (symbol) occurrence in the root sequent $s_r$ of $T$.
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

1\.\ case: $Γ ⊃ Δ ≡ P, Γ' ⊃ Δ', P$ is an axiom $(Ax)$. Then $P$, $P
→ ⋁Δ' ∨ P$, $⋁Δ' ∨ P ≡ ⋁Δ$ is the required LP derivation.
^[TODO usage of $≡$ for sequents here and following cases is confusing]

2\.\ case: $Γ ⊃ Δ ≡ ⊥, Γ' ⊃ Δ$ is an axiom $(⊥ ⊃)$. Then $⊥$, $⊥ → ⋁Δ$, $⋁Δ$ is
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
by a (lift) rule. By the precondition on $t$ there exists a
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
subformulas and variables already occurring in $T$. For cases 1 and 2
this is immediate as the given derivations directly use subformulas
from $T$. In cases 3, 4 and 5, the starting derivations do not
introduce new variables by induction hypothesis and the use of the
deduction theorem does not introduce new variables by corollary
\ref{dedvar}. The derivation for case 6 is already included in the
corollary and therefore trivially does not introduce new variables.
\End{proof}

The proofs for the following standard lemmas for G3lift exactly mirror
the proofs for the same lemmas for G3s, as G3lift exactly
mirrors G3s. The only trivial difference is that the precondition of
the (lift) rule has to be checked whenever a different/new (lift)
rule gets introduced. Because of this and also because the following
result is just included for completeness and not actually used in the
remaining of the text, we will omit the proofs here and refer the
reader to the proofs for $G3s$ in @pulver2010 [40ff.] as well as later
in this text.

\Begin{lemma}[weakening for G3lift] \label{liftweak}
$G3lift ⊢ Γ ⊃ Δ ⇒ G3lift ⊢ Γ, Γ' ⊃ Δ, Δ'$
\End{lemma}

\Begin{lemma}[inversion for G3lift] \label{liftinverse}

* $G3lift ⊢ Γ ⊃ Δ, A → B ⇒ G3lift ⊢ A, Γ ⊃ Δ, B$

* $G3lift ⊢ A → B, Γ ⊃ Δ ⇒ G3lift ⊢ Γ ⊃ Δ, A \text{ and } G3lift ⊢ B, Γ ⊃ Δ$

* $G3lift ⊢ t:A, Γ ⊃ Δ ⇒ G3lift ⊢ A, t:A, Γ ⊃ Δ$

* $G3lift ⊢ Γ ⊃ Δ, t:A ⇒ G3lift ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{lemma}[contraction for G3lift] \label{liftcontr}

* $G3lift ⊢ A, A, Γ ⊃ Δ ⇒ G3lift ⊢ A, Γ ⊃ Δ$

* $G3lift ⊢ Γ ⊃ Δ, A, A ⇒ G3lift ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{lemma}[cut elimination for G3lift] \label{liftcut}
If $G3lift ⊢ A, Γ ⊃ Δ$ and $G3lift ⊢ Γ' ⊃ Δ', A$ then $G3lift ⊢ Γ,Γ' ⊃ Δ,Δ'$.
\End{lemma}

\Begin{lemma} \label{liftgenax}
$G3lift ⊢ A, Γ ⊃ Δ, A$ for any LP formula $A$.
\End{lemma}

\Begin{theorem} \label{equiv2}
$Γ ⊢_{LP} A ⇒ G3lift ⊢ Γ ⊃ A$
\End{theorem}

\Begin{proof}
By complete induction over the length of the derivation $d$ for $Γ ⊢_{LP} A$.

1\.\ case $A$ is an axiom A0. By the completeness of G3c included in
G3lift there exists a derivation of $Γ ⊃ A$ and $⊃ A$ using the subset G3c.

2\.\ case $A$ is an axiom $A1-A4$. As the derivations in figure
\ref{axiomproofs} show, $⊃ A$ can be derived for each axiom using
lemma \ref{liftgenax} for the base cases. $Γ ⊃ A$ follows from
weakening (\ref{liftweak}).

\begin{figure} \caption{G3lift proofs for LP axioms} \label{axiomproofs}
\begin{longtable}{cc}

\AXC{$F, t{:}F ⊃ F$}
\RightLabel{$(:⊃)$}
\UIC{$t{:}F ⊃ F$}
\RightLabel{$(⊃→)$}
\UIC{$⊃ t{:}F → F$}
\DP

&

\AXC{$F, t{:}F ⊃ F$}
\RightLabel{$(:⊃)$}
\UIC{$t{:}F ⊃ F$}
\RightLabel{(lift)}
\UIC{$t{:}F ⊃ t{:}F$}
\RightLabel{(lift)}
\UIC{$t{:}F ⊃ !t{:}t{:}F$}
\RightLabel{$(⊃→)$}
\UIC{$⊃ t{:}F → !t{:}t{:}F$}
\DP

\\[30pt]

\AXC{$F, t{:}F ⊃ F$}
\RightLabel{$(:⊃)$}
\UIC{$ t{:}F ⊃ F$}
\RightLabel{(lift)}
\UIC{$ t{:}F ⊃ (s + t)F$}
\RightLabel{$(⊃→)$}
\UIC{$⊃ t{:}F → (s + t)F$}
\DP

&

\AXC{$F, s{:}F ⊃ F$}
\RightLabel{$(:⊃)$}
\UIC{$ s{:}F ⊃ F$}
\RightLabel{(lift)}
\UIC{$ s{:}F ⊃ (s + t)F$}
\RightLabel{$(⊃→)$}
\UIC{$⊃ s{:}F → (s + t)F$}
\DP

\end{longtable}

\begin{center}
\AXC{$F, s{:}(F→G), t{:}F ⊃ G, F$}
\RightLabel{$(:⊃)$}
\UIC{$s{:}(F→G), t{:}F ⊃ G, F$}
\AXC{$G, s{:}(F→G), t{:}F ⊃ G$}
\RightLabel{$(→⊃)$}
\BIC{$F→G, s{:}(F→G), t{:}F ⊃ G$}
\RightLabel{$(:⊃)$}
\UIC{$s{:}(F→G), t{:}F ⊃ G$}
\RightLabel{(lift)}
\UIC{$s{:}(F→G), t{:}F ⊃ s⋅t{:}G$}
\RightLabel{$(⊃→)$}
\UIC{$s{:}(F→G) ⊃ t{:}F → s⋅t{:}G$}
\RightLabel{$(⊃→)$}
\UIC{$⊃ s{:}(F→G) → (t{:}F → s⋅t{:}G)$}
\DP
\end{center}
\end{figure}

3\.\ case $A ∈ Γ$ is an assumption. We get the required proof for $A,
Γ' ⊃ A$ directly from lemma \ref{liftgenax}.

4\.\ case $A ≡ c:A_0$ is derived by rule R1 (Axiom Necessitation). Then
$A_0$ is an axiom and there is a G3lift proof for $⊃ A_0$ by induction
hypothesis. Appending a (lift) rule gives a G3lift proof
for $Γ ⊃ c:A_0$.

5\.\ case $A$ is derived by rule R0 (Modus Ponens). By induction
hypothesis, we have G3lift proofs for $Γ ⊃ B → A$ and $Γ ⊃ B$ for the
premises of the modus ponens rule. By the inversion lemma we get a
G3lift proof for $B, Γ⊃ A$ and by cut elimination and contraction we
get the required proof for $Γ ⊃ A$.
\End{proof}


Annotated S4 Formulas and Proofs
================================

\Begin{definition}[polarity]
We assign a *positive* or *negative polarity* relative to $A$ to all
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
  opposite polarity relative to the sequent $Γ ⊃ Δ$ as the same
  occurrence $B$ in the formula $A$ has relative to $A$.

* An occurrence of a subformula $B$ in a formula $A$ in $Δ$ has the
  same polarity relative to the sequent $Γ ⊃ Δ$ as the same
  occurrence $B$ in the formula $A$ has relative to $A$.

\End{definition}

This gives the subformulas of a sequent $Γ ⊃ Δ$ the same polarity as
they would have in the equivalent formula $⋀Γ → ⋁Δ$. Also notice that
for the derived operaters all subformulas have the same polarity,
except for $¬$ which switches the polarity for its subformula.

^[TODO explain
used syntax and equivalence or remove]

The rules of S4 respect the polarities of the subformulas, so that all
corresponding occurrences of subformulas have the same polarity
throughout the proof. We therefore assign positive polarity to
families of positive occurrences and negative polarity to families of
negative occurrences. Moreover, positive families in a S4 proof which
have occurrences introduced by a $(⊃ □)$ rule are called principal
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
tree by distinguishing all $□$ occurrences as separate families and
dropping the distinction between principal positive and non-principal
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


So for example the annotated version of $□((R → □R) → ⊥) → ⊥$ is
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
$r_A$ and a constant specification of all constants occurring in $r_A$
with $A^r := r_A(an_A(A))$.

\Begin{definition}[normal]
A realization function is *normal* if all symbols for negative families
and non-principal positive families are mapped to distinct
proof variables. A LP-realization is *normal* if the corresponding
realization function is normal and the $CS$ is injective. ^[TODO
probably should not misuse normal here for non-principal positive families]
\End{definition}

\Begin{theorem}[Realization] \label{realization}
If $S4 ⊢ A$ then $LP ⊢ A^r$ for some normal
LP-realization $r$.
\End{theorem}

\Begin{proof}
Because of $S4 ⊢ A$ and the completeness of G3s, there
exists a G3s proof $𝒯 = (T, R)$ of $⊃ A$.

For all principal families $⊞_i$ in $an_T(T)$, enumerate the
$(⊃ □)$ rules principally introducing an occurrence of $⊞_i$ as
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
proof as none of the (lift) rules fulfill the necessary precondition
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

Moreover, this precondition remains fulfilled for the $(⊃ :)$ rule
$R_{i,j}$ in any proof tree $r_T^k(an_T(T))$ for $k > ε(i,j)$ again by
the substitution lemma \ref{subst}.

For the final normal realization function $r_T^N$ and injective
constant specification $CS^N$ we have that $r_T^N(an_T(T))$ is a
correct G3lift proof based on $CS^N$ of $⊃ r_T(A)$. So by theorem
\ref{equiv1} of G3lift we have $LP ⊢ A^r$ for the normal LP-realization
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


Self-referentiality of S4
=========================

The formulation of LP allows for proof terms $t$ to justify formulas
$A(t)$ about themself. This leads to the possibility of
self-referential constant specifications in the following sense:

\Begin{definition}[directly self-referential]
A constant specification $CS$ is *directly self-referential* if there is a
constant $c$ such that $c:A(c) ∈ CS$.
\End{definition}

\Begin{definition}[self-referential]
A constant specification $CS$ is *self-referential* if there is a
subset $A ⊆ CS$ such that $A := {c_0:A(c_1), ..., c_{n-1}:A(c_0)}$.
\End{definition}

The following theorem from @brezhnev2006 [31] shows that
self-referential constant specifications are necessary to realize S4:

\Begin{theorem}
The S4 theorem $¬□(P ∧ ¬□P)$ can not be realized without a directly
self-referential constant specification.
\End{theorem}

We will not reproduce this general result but use the provided formula
as an example for an inherently self-referential S4 formula.  If we
look at the G3s proof for $¬□(P ∧ ¬□P)$ and the realization of that
proof in figure \ref{proofs}, we can see why a self referential proof
term like the used term $t$ for the propositional tautology $P ∧
¬t⋅x{:}P → P$ is necessary. In order to prove $¬□(P ∧ ¬□P)$ we have to
disprove $P ∧ ¬□P$ at some point which means we have to prove
$□P$. The only way to prove $□P$ is using $□(P ∧ ¬□P)$ as an
assumption on the left. This leads to the situation that we introduce
$□$ by a $(⊃ □)$ rule where the same family already occurs on the
left. As the following chapters will show formally such a situation is
actually necessary for the self-referentiality of an S4 formula.

\begin{figure} \caption{proof for $¬□(P ∧ ¬□P)$} \label{proofs}
\begin{longtable}{cc}
\AXC{$P, ¬□P, □(P∧¬□P) ⊃ P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬□P, □(P∧¬□P) ⊃ P$}
\RightLabel{$(□ ⊃)$}
\UIC{$□(P∧¬□P) ⊃ P$}
\RightLabel{$(⊃ □)$}
\UIC{$P, □(P∧¬□P) ⊃ □P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬□P, □(P∧¬□P) ⊃$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬□P, □(P∧¬□P) ⊃$}
\RightLabel{$(□ ⊃)$}
\UIC{$□(P ∧ ¬□P) ⊃$}
\RightLabel{$(⊃ ¬)$}
\UIC{$⊃ ¬□(P ∧ ¬□P)$}
\DP

&

\AXC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ P$}
\RightLabel{$(: ⊃)$}
\UIC{$x{:}(P ∧ ¬t⋅x{:}P) ⊃ P$}
\RightLabel{$(lift)$}
\UIC{$P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ t⋅x{:}P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(: ⊃)$}
\UIC{$x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(⊃ ¬)$}
\UIC{$⊃ ¬x{:}(P ∧ ¬t⋅x{:}P)$}
\DP
\end{longtable}
\end{figure}



Prehistoric Phenomena
=====================

\Begin{definition}[History]
In branch $s$ of the form $s_rR^*O_{i,j}RI_{i,j}R^*s$ in a
G3s−proof $T$, the path $s_rR^*O_{i,j}$ is called a *history* of $p_i$
in branch $s$. The remaining sequents $I_{i,j}R^*s$ is called a
*pre-history* of $p_i$ in branch $s$. ^[see @yu2010, 389]
\End{definition}

\Begin{definition}[Prehistoric Relation] \label{local}
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
(⇒): $⊞_h$ occurs in a sequent $s'$ in a pre-history of $p_i$ in the
path $s$, so the path $s$ has the form
$s_rR^*O_{i,j}RI_{i,j}R^*s'R^*s$ for some $j ≤ n_i$. By the subformula
theorem \ref{sub}, there is an occurrence of $⊞_h$ in $I_{i,j}$ as
$s'$ is part of $T↾I_{i,j}$. If this occurrence is on the left we have
$h ≺^s_L i$, if it is on right we have $h ≺^s_R i$. In both cases $h
≺^s i$ holds.

(⇐): By definition there is a $I_{i,j}$ in $s$, where $⊞_h$ occurs
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
the subformula property there is only one occurrence of $⊞_i$ in the
root sequent.
\End{proof}

\Begin{lemma} \label{trans}
If $k ≺_R j$ and $j ▹ i$, then $k ▹ i$, where $▹$ is any one of $≺$, $≺_L$, $≺_R$, $≺^s$ , $≺^s_L$ or $≺^s_R$.
\End{lemma}

\Begin{proof}
Since $k ≺_R j$, there is a $⊞_k$ occurring in the scope of a
principally introduced $⊞_j$. All corresponding occurrences of $⊞_j$
are part of corresponding occurrences of the subformula $⊞_jA(⊞_kB)$,
with exactly one occurrence in the root sequent $s_r$ by the
subformula property \ref{sub}. So wherever $⊞_j$ occurs in the proof
$T$, there is a $⊞_k$ occurring in the scope of it.

For any $▹$, we have $j ▹ i$ because some occurrence of $⊞_j$ in a
subformula of the premise of a rule $R_{i,q}$. By the previous
statement there is also an occurrence of $⊞_k$ in the same scope, and
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
families $p_i$ in the given topological order $k_x$ fulfills the
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
1}(an_T(I_{i,j}))$. For any $⊞_h$ occurring in $I_{i,j}$, we have by
definition $h ≺ i$, and therefore by lemma \ref{epsilon} $ε(h,j_h) ≤
ε(i,j)$ for all $j_h ≤ m_h$. So any provisional variable $u_{h,j_h}$
occurring in $r_T^0(an_T(I_{i,j}))$ is already replaced in $r_T^{ε(i,j)
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


Prehistoric relations in G3s with cut rules
===========================================

In this chapter we will define prehistoric relations in the system G3s
+ (Cut). The (context sharing) cut rule has the following definition
[@troelstra2000 67]:

\Begin{definition}[$(Cut)$ rule]

\AXC{$G3s ⊢ Γ ⊃ Δ, A$}
\AXC{$G3s ⊢ A, Γ ⊃ Δ$}
\RightLabel{$(Cut)$}
\BIC{$G3s ⊢ Γ ⊃ Δ$}
\DP

\End{definition}

It is necessary to expand the definition of correspondence
(\ref{corr}) to $(Cut)$ rules as follows:

\Begin{definition}[correspondence for $(Cut)$]

* The active formulas (and their symbols) in the premises of a $(Cut)$ rule correspond
to each other.

\End{definition}

Neither classification and annotations for families of $□$ nor the
definition of prehistoric relation carry over directly to G3s +
$(Cut)$. The classification and annotations do not carry over as the
$(Cut)$ rule uses the cut formula in different polarities for the two
premises.  The prehistoric relations do not carry over as the $(Cut)$
formula no longer fulfills the subformula property used for proofing
lemma \ref{prehist}. Because of this we will use the following global
definition for prehistoric relations between any two $□$ families in a
G3s + $(Cut)$ proof:

\Begin{definition}[Prehistoric Relation in G3s + $(Cut)$] \label{global}
A family $□_i$ has a *prehistoric relation* to another family $□_j$, in
notation $i ≺ j$, if there is a $(⊃ □)$ rule introducing an occurrence
of $□_j$ with premise $s$, such that there is an occurrence of $□_i$
in $T↾s$.
\End{definition}

Notice that there can be prehistoric relations with $□$ families which
locally have negative polarity, as the family could be part of a cut
formula and therefore also occur with positive polarity in the other
branch of the cut. Also there can be prehistoric relations with
families not occurring in the relevant $(⊃ □)$ rule because the
family in question is part of a cut formula which was already cut.
Finally, adding prehistoric relations with negative families
in a cut free G3s proof does not introduce prehistoric loops, as in
G3s a negative family is never introduced by a $(⊃ □)$ rule and
therefore has no prehistoric families itself.

We do not have any transitivity results for global prehistoric
relations, as two prehistoric relations involving the same family can
emerge from completely different branches of the proof.

To handle proof terms $s⋅t$ in the next chapter, we will also need a
rule for modus ponens under $□$. We therefore introduce here the
new rule $(□Cut)$ as follows:

\Begin{definition}[$(□Cut)$ rule]

\AXC{$G3s ⊢ Γ ⊃ Δ, □A$}
\AXC{$G3s ⊢ Γ ⊃ Δ, □(A → B)$}
\RightLabel{$(□Cut)$}
\BIC{$G3s ⊢ Γ ⊃ Δ, □B$}
\DP

\End{definition}

Again it is also necessary to expand the definition of correspondence
(\ref{corr}) for this rule:

\Begin{definition}[correspondence for $(□Cut)$] \label{boxcutcorr}

* The topmost $□$ occurrence in the active formulas and the principal
  formula correspond to each other.

* The subformulas $A$ in the active formula of the premises correspond
  to each other.

\End{definition}

Notice that with this expansion, $□$ occurrences of the same family no
longer are always part of the same subformula $□C$. Also similar to
the $(Cut)$ rule, we add correspondence between negative and positive
occurrences of $□$ symbols.

With the following lemmas and theorems we will establish a
constructive proof for $G3s + (□Cut) ⊢ Γ ⊃ Δ ⇒ G3s + (Cut) ⊢ Γ ⊃ Δ ⇒
G3s ⊢ Γ ⊃ Δ$. Moreover there will be corollaries showing that the
constructions do not introduce prehistoric loops in the global sense
given above. By lemma \ref{prehist} the global definition \ref{global}
and the original local definition \ref{local} are equivalent in G3s
and therefore the G3s proof for $Γ ⊃ Δ$ will be prehistoric loop
free by the original definition if the proof in G3s + $(□Cut)$ was
prehistoric loop free.

It is important to note, that all the following corollaries are not
restricted to the annotations $an_T$ of the proofs $𝒯 = (T, R)$ given
by the premise of the lemma but still hold for arbitrary annotations
$an$. That means there is no implicit assumption that the families
have only a single occurrence in the sequents of the lemma or theorem
and the results can also be used in subtrees $T↾s$ together with an
annotation $an_T$ for the complete tree.

\Begin{lemma}[weakening for G3s] \label{weak}
$G3s ⊢ Γ ⊃ Δ ⇒ G3s ⊢ Γ, Γ' ⊃ Δ, Δ'$
\End{lemma}

\Begin{proof}
By structural induction on the proof tree:

1\.\ case: $Γ ⊃ Δ$ is an axiom. Then also $Γ, Γ' ⊃ Δ, Δ'$ is an axiom.

2\.\ case: $Γ ⊃ Δ$ is proven by a rule different from $(⊃ □)$. Use the
induction hypothesis on the premises and append the same rule for a
proof of $Γ, Γ' ⊃ Δ, Δ'$.

3\.\ case: $Γ ⊃ Δ$ is proven by a $(⊃ □)$ rule. Add Γ' and Δ' as
weakening formulas to the rule for a proof of $Γ, Γ' ⊃ Δ, Δ'$.
\End{proof}

\Begin{lcorollary} \label{weakprehist}
For any annotation $an$ the proof for $G3s ⊢ Γ, Γ' ⊃ Δ, Δ'$ as
constructed in the main proof has the exact same prehistoric relations
as the original proof for $G3s ⊢ Γ ⊃ Δ$. ^[TODO compare with
"weakening occurrences are isolated" in @yu2017 [787]]
\End{lcorollary}

\Begin{proof}
$(⊃ □)$ rules are handled by the 3\.\ case by new $(⊃ □)$ rules that
use the exact same proof for the premise and only in the history add
the new weakening formulas. So all prehistoric branches are unchanged and
all prehistoric relations remain the same.
\End{proof}


\Begin{lemma}[inversion for G3s] \label{invers}

* $G3s ⊢ Γ ⊃ Δ, A → B ⇒ G3s ⊢ A, Γ ⊃ Δ, B$

* $G3s ⊢ A → B, Γ ⊃ Δ ⇒ G3s ⊢ Γ ⊃ Δ, A \text{ and } G3s ⊢ B, Γ ⊃ Δ$

* $G3s ⊢ □A, Γ ⊃ Δ ⇒ G3s ⊢ A, □A, Γ ⊃ Δ$

* $G3s ⊢ Γ ⊃ Δ, □A ⇒ G3s ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{proof}
For any formula $C$ to inverse, we proof the lemma by structural
induction on the proof tree:

1\.\ case: $C$ is weakening formula of the last rule. Just weaken in
the necessary deconstructed formulas instead.

2\.\ case: $C$ is a side formula of the last rule. By induction
hypothesis we can replace $C$ by the necessary deconstructed formulas
in the premises and append the same rule to get the necessary proof(s).

3\.\ case: $C$ is the principal formula of the last rule. Then
proof(s) of the premise(s) without the last rule is/are already the
necessary proof(s).
\End{proof}

\Begin{lcorollary} \label{inversprehist}
For any annotation $an$ the constructed proofs do not introduce any
new prehistoric relations.
\End{lcorollary}

\Begin{proof}
In the 1\. case we only remove occurrences of $□$ so no new
prehistoric relations are introduced. In the 2\.\ case no new
prehistoric relations are introduced by the induction
hypothesis. Moreover in the case of a $(⊃ □)$ rule, all occurrences in
the prehistory of the new rule also occur in the prehistory of the
original rule. In the 3\.\ case, a rule is removed, which again can
not introduce new prehistoric relations.
\End{proof}

\Begin{lemma}[contraction for G3s] \label{contr}

* $G3s ⊢ A, A, Γ ⊃ Δ ⇒ G3s ⊢ A, Γ ⊃ Δ$

* $G3s ⊢ Γ ⊃ Δ, A, A ⇒ G3s ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{proof}
By simultaneous induction over the proof tree and the build up of $A$:

1\.\ case: At least one occurrence of $A$ is a weakening formula of the
last rule. Just remove it. Note that this case also covers all axioms.

2\.\ case: Both occurrences of $A$ are side formulas of the last
rule. By induction hypothesis the premises of the rule are provable
with the two $A$ contracted. Append the same rule for the necessary proof.

3\.\ case: One of the occurrences of $A$ is the principal formula of
the last rule, the other is a side formula. Use the inversion lemma
(\ref{invers}) on the side formula $A$ in the premises and the
induction hypothesis to contract the deconstructed parts of
$A$. Append the same last rule without $A$ as side formula to get the
necessary proof.
\End{proof}

\Begin{lcorollary} \label{contrprehist}
For any annotation $an$ the constructed proofs do not introduce any
new prehistoric relations.
\End{lcorollary}

TODO decide for a proof, adapt main proof for correspondence?

\Begin{proof}
In the 1\. case we only remove occurrences of $□$ so no new
prehistoric relations are introduced. In the 2\.\ case no new
prehistoric relations are introduced by the induction
hypothesis. Moreover in the case of a $(⊃ □)$ rule, all occurrences in
the prehistory of the new rule also occur in the prehistory of the
original rule. In the 3\.\ case,  by corollary \ref{inversprehist} no
new prehistoric relations are introduced for the new proof where both
occurrences of $A$ are deconstructed. Moreover, in the case of
appending a $(⊃ □)$ rule, all occurrences in the new proof are also in
the old proof and therefore no new prehistoric relations get introduced.
\End{proof}

\Begin{proof}
The algorithm implicitly described in the main proof is as follows:

1. Remove all corresponding subformulas of one of the $A$ in the final
sequent from the proof.

2. Remove any rule used for the build up of the same final occurrence
of $A$ from the proof (from the first step the active formulas and the
principal formula of all this rules are already removed).

As the new proof is in a way a strict subset of the old proof, no new
prehistoric relations can be introduced.
\End{proof}

\Begin{lemma} \label{drop}
$G3s ⊢ B, □B, Γ ⊃ Δ ⇔ G3s ⊢ B, Γ ⊃ Δ$
\End{lemma}

\Begin{proof}
The $(⇐)$ direction is just a weakening. The $(⇒)$ direction is shown
by a structural induction over the proof tree for $B, □B, Γ ⊃ Δ$:

1\.\ case: $□B$ is a weakening formula of the last rule. Then removing
it keeps the proof intact.

2\.\ case: $□B$ is a side formula of the last rule. By induction hypothesis
the premises of the rules are provable without $□B$. Append the same
rule to get a proof of $B, Γ ⊃ Δ$.

3\.\ case: $□B$ is the principal formula of the last rule, then the premise
is $B, B, □B, Γ ⊃ Δ$. By induction hypothesis we get a proof for
$B, B, Γ ⊃ Δ$ and by contraction we get $B, Γ ⊃ Δ$.
\End{proof}

\Begin{lcorollary} \label{dropprehist}
For any annotation $an$ the constructed proof does not introduce any
new prehistoric relations.
\End{lcorollary}

\Begin{proof}
The new proof is the old proof with $□B$ removed and $□ ⊃$ rules with
$□B$ as principal formula replaced by contractions, which do not
introduce new prehistoric relations by corollary \ref{contrprehist}.
So the new proof can not introduce any new prehistoric relations.
\End{proof}

\Begin{theorem}[cut elimination for G3s] \label{cut}
If $G3s ⊢ Γ ⊃ Δ, A$ and $G3s ⊢ A, Γ ⊃ Δ$ then $G3s ⊢ Γ ⊃ Δ$.
\End{theorem}

\Begin{proof}
By a simultaneous induction over the depths of the proof trees $𝒯_L$
for $Γ ⊃ Δ, A$ and $𝒯_R$ for $A, Γ ⊃ Δ$ as well as the rank of $A$
(i.e we will use the induction hypothesis to cut with the same
formulas but shorter proof trees as well as to cut proof trees with
lower rank formulas):

1\.\ case: $A$ is a weakening formula in the last rule of one of the
proofs. We get the required proof for $Γ ⊃ Δ$ by leaving out $A$ from
that proof.

2\.\ case: $A$ is a side formula in the last rule of one of the two
proofs. We distinguish the follow ing subcases:

2\.1 case: $A$ is a side formula in the last rule of $𝒯_R$, which is
not a $(⊂ □)$ rule. By induction hypothesis we can cut the weakened
premises $A, Γ_i, Γ ⊃ Δ_i, Δ$ of that rule with a weakened $Γ_i, Γ ⊃
Δ_i, Δ, A$ proven by $𝒯_L$ to get $Γ_i, Γ ⊃ Δ_i, Δ$. Applying the same
rule we get the a proof for $Γ,Γ ⊃ Δ,Δ$. By contraction we get a proof
for $Γ ⊃ Δ$.

2\.2 case: $A$ is a side formula in the last rule of $𝒯_L$.  This case
is handled symmetrical to the previous one. Notice that the last rule
can not be a $(⊃ □)$ rule in this case, as that rule does not have any
side formulas on the right.

2\.3 case: $A$ is a side formula in the last rule of $𝒯_R$, which is a
$(⊃ □)$ rule and a principal formula in the last rule of $𝒯_L$. Then
$A$ has the form $□A_0$ as it is a side formula of a $(⊃ □)$ on the
right. So the last rule of $𝒯_L$ is also a $(⊃ □)$ rule and the proof
has the following form:

\AXC{$𝒯_L$} \noLine
\UIC{$□Γ_L ⊃ A_0$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ'_L, □Γ_L ⊃ Δ', □B, □A_0$}

\AXC{$𝒯_R$} \noLine
\UIC{$□A_0, □Γ_R ⊃ B$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ'_R, □A_0, □Γ_R ⊃ Δ', □B$}

\RightLabel{$(cut)$}
\BIC{$Γ ⊃ Δ', □B$}
\DP
where $Δ = Δ', □B$ and $Γ = Γ'_L, □Γ_L = Γ'_R, □Γ_R$.

We can move the cut up on the right using weakening as follows:

\AXC{$𝒯_L$} \noLine
\UIC{$□Γ_L ⊃ A_0$}
\RightLabel{$(⊃ □)$}
\UIC{$□Γ_R, □Γ_L ⊃ B, □A_0$}

\AXC{$𝒯'_R$} \noLine
\UIC{$□A_0, □Γ_R, □Γ_L ⊃ B$}

\RightLabel{$(cut)$}
\BIC{$□Γ_R, □Γ_L ⊃ B$}

\RightLabel{$(⊃ □)$}
\UIC{$Γ, □Γ_R, □Γ_L ⊃ Δ', □B$}
\DP

By the induction hypothesis and a contraction we get the required
proof for $Γ ⊃ Δ$ as $□Γ_L ⊆ Γ$ and $□Γ_R ⊆ Γ$.

3\.\ case: $A$ is the principal formula in the last rules of $𝒯_L$ and
$𝒯_R$. Then we have the following subcases:

3\.1: The last rules are axioms. Then $A$ is atomic and $A ∈ Δ$ and $A
∈ Γ$ as there is no axiom with a principal $⊥$ on the
right. Therefore also $Γ ⊃ Δ$ is an axiom.

3\.2:  $A$ has the form $A_0 → A_1$. Then the proof has the following form:

\AXC{$𝒯_L$} \noLine
\UIC{$A_0, Γ ⊃ Δ, A_1$}
\RightLabel{$(⊃ →)$}
\UIC{$Γ ⊃ Δ, A_0 → A_1$}

\AXC{$𝒯_{R1}$} \noLine
\UIC{$Γ ⊃ Δ, A_0$}
\AXC{$𝒯_{R2}$} \noLine
\UIC{$A_1, Γ ⊃ Δ$}
\RightLabel{$(→ ⊃)$}
\BIC{$A_0 → A_1, Γ ⊃ Δ$}

\RightLabel{$(Cut)$}
\BIC{$Γ ⊃ Δ$}
\DP

Using weakening and two cuts with the lower rank formulas $A_0$ and $A_1$ we can
transform that into:

\AXC{$𝒯'_{R1}$} \noLine
\UIC{$Γ ⊃ Δ, A_1, A_0$}
\AXC{$𝒯_L$} \noLine
\UIC{$A_0, Γ ⊃ Δ, A_1$}
\RightLabel{$(Cut)$}
\BIC{$Γ ⊃ Δ, A_1$}
\AXC{$𝒯_{R2}$} \noLine
\UIC{$A_1, Γ ⊃ Δ$}
\RightLabel{$(Cut)$}
\BIC{$Γ ⊃ Δ$}
\DP

Using the induction hypothesis we get the required cut-free proof for
$Γ ⊃ Δ$.

3\.3:  $A$ has the form $□A_0$. Then the proof has the following form:


\AXC{$𝒯_L$} \noLine
\UIC{$□Γ_0 ⊃ A_0$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ_1, □Γ_0 ⊃ Δ, □A_0$}

\AXC{$𝒯_R$} \noLine
\UIC{$A_0, □A_0, Γ ⊃ Δ$}
\RightLabel{$(□ ⊃)$}
\UIC{$□A_0, Γ ⊃ Δ$}

\RightLabel{$(Cut)$}
\BIC{$Γ ⊃ Δ$}
\DP

From the lemma \ref{drop}, we get a proof $𝒯'_R$ for $A_0, Γ ⊃ Δ$
and by weakening we get a proof $𝒯'_L$ for $Γ ⊃ Δ, A_0$. From this and
using a cut with the lower rank formula $A_0$ we get the following
proof:

\AXC{$𝒯'_L$} \noLine
\UIC{$Γ ⊃ Δ, A_0$}
\AXC{$𝒯'_R$} \noLine
\UIC{$A_0, Γ ⊃ Δ$}
\RightLabel{$(Cut)$}
\BIC{$Γ ⊃ Δ$}
\DP

Using the induction hypothesis we get the required cut-free proof for
$Γ ⊃ Δ$.
\End{proof}


\Begin{corollary} \label{cutprehist}
For any annotation $an$ the constructed proof for $Γ ⊃ Δ$ only
introduces new prehistoric relations $i ≺ j$ between families $□_i$
and $□_j$ occurring in $Γ ⊃ Δ$ where there exists a family $□_k$ in
$A$ such that $i ≺ k ≺ j$ in the original proof.
\End{corollary}

\Begin{proof}
The used weakenings and contractions do not introduce any new
prehistoric relations by the corollaries \ref{weakprehist} and
\ref{contrprehist}. Also leaving out formulas as in case 1 and 3.1, as
well as rearranging rules which are not $(⊃ □)$ rules as in case 3.2
do not introduce any new prehistoric relations.  Finally the use of
lemma \ref{drop} in case 3.3 does not introduce any new prehistoric
relations by corollary \ref{dropprehist} and leaving out the $(⊃ □)$
rule also can not introduce any new prehistoric relations.

So the only place where new prehistoric relations get introduced is by
the new $(⊃ □)$ in case 2.3. All prehistoric relations from $T_R$ are
already present from the $(⊃ □)$ rule on the right in the original
proof. So only prehistoric relations from $T_L$ are new. For all
families $□_i$ in the prehistory $T_L$ we have $i ≺ k$ for the
family $□_k$ in the cut formula introduced by the $(⊃ □)$ rule on the
left. Moreover, we have $k ≺ j$ for the same family because of the
occurrence of $□A_0$ on the right.
\End{proof}

\Begin{corollary} \label{cutloop}
For any annotation $an$ the constructed proof for $Γ ⊃ Δ$ does not
introduce prehistoric loops.
\End{corollary}

\Begin{proof}
Assume for contradiction that there exists a prehistoric loop $i_0 ≺
... ≺ i_{n-1} ≺ i_0$ in the new proof. By the previous lemma for any
prehistoric relation $i_k ≺ i_{k+1 \mod n}$ in the loop either $i_k ≺
i_{k+1 \mod n}$ in the old proof or there is a family $i'_k$ in the
cut formula such that $i_k ≺ i'_k ≺ i_{k+1 \mod n}$. Therefore we also
have a prehistoric loop in the original proof.
\End{proof}

\Begin{theorem}[$(□Cut)$ elimination] \label{boxcut}
If $G3s ⊢ Γ ⊃ Δ, □A$ and $G3s ⊢ Γ ⊃ Δ, □(A → B)$ then $G3s ⊢ Γ ⊃ Δ, □B$
\End{theorem}

\Begin{proof}
By a structural induction over the proof trees $𝒯_L$ for
$Γ ⊃ Δ, □A$ and $𝒯_R$ for $Γ ⊃ Δ, □(A → B)$.

1\.\ case: $□(A → B)$ or $□A$ is a weakening formula of the last
rule. Just weaken in $□B$ instead in that proof.

2\.\ case: $□(A → B)$ or $□A$ is a side formula of the last rule.
Use the induction hypothesis on the premises of that rule with the
other proof and append the same rule.

3\.\ case: $□(A → B)$ and $□A$ are the principal formula of the last
rule. Then the last rules have the following form:

\AXC{$𝒯_L$} \noLine
\UIC{$□Γ_L ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ_L', □Γ_L  ⊃ Δ, □A$}

\AXC{$𝒯_R$} \noLine
\UIC{$□Γ_R ⊃ A → B$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ'_R, □Γ_R  ⊃ Δ, □(A → B)$}

\RightLabel{$(□cut)$}
\BIC{$Γ ⊃ Δ, □B$}
\DP
where $Δ = Δ', □B$ and $Γ = Γ'_L, □Γ_L = Γ'_R, □Γ_R$.

By inversion for $(⊃ →)$ we get a proof $𝒯'_R$ for $A, □Γ_R ⊃ B$ from
the first premise $□Γ_R ⊃ A → B$.  Using weakening and a normal cut on
the formula $A$ we get the following proof:

\AXC{$𝒯'_L$} \noLine
\UIC{$□Γ_L, □Γ_R ⊃ A$}
\AXC{$𝒯''_R$} \noLine
\UIC{$A, □Γ_L, □Γ_R  ⊃ B$}
\RightLabel{$(Cut)$}
\BIC{$□Γ_L, □Γ_R ⊃ B$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ, □Γ_L, □Γ_R ⊃ Δ, □B$}
\DP

By contraction and a cut elimination we get the required G3s proof for
$Γ ⊃ Δ, □B$ as $□Γ_L ⊆ Γ$ and $□Γ_R ⊆ Γ$.
\End{proof}

\Begin{corollary} \label{boxcutloop}
For any annotation $an$ the constructed proof for $Γ ⊃ Δ$ does not
introduce prehistoric loops.
\End{corollary}

\Begin{proof}
Replacing $□(A→B)$ or $□A$ with $□B$ in weakening formulas or side
formulas does not change prehistoric relations as the two $□$-symbols
belong to the same family.

Any prehistoric relation because of the new $(⊃ □)$ in case 3 already
exists in the original proof, as every $□$ occurrence in the new
prehistory was in one of the two prehistories of $□A$ and $□(A → B)$
of the original proof.

So the new proof with $(□Cut)$ rules replaced by $(Cut)$ rules does
not introduce new prehistoric relations and therefore also no new
prehistoric loops. By corollary \ref{cutloop}, the cut elimination to
get a G3s proof does not introduce prehistoric loops.
\End{proof}

\Begin{definition}
The cycle-free fragment of a system $Y$, denoted by $Y^⊗$, is the
collection of all sequents that each has a prehistoric-cycle-free
$Y$-proof [@yu2017 787].
\End{definition}

\Begin{theorem}
The cycle-free fragments of $G3s + (□Cut)$, $G3s + (Cut)$ and $G3s$ are
identical.
\End{theorem}

\Begin{proof}

A prehistoric-cycle-free proof in $G3s$ by the original local
definition (\ref{local}) is also prehistoric-cycle-free by the the
global definition (\ref{global}) by lemma \ref{prehist} and because in
a $G3s$-proof a negative family can not have prehistoric relations
^[TODO on the left, smaller, what terminology to use?]. So any sequent
$Γ ⊂ Δ ∈ G3s^⊗$ is trivially also provable prehistoric-cycle-free in
$G3s + (Cut)$ and $G3s + (□Cut)$ and we have $G3s^⊗ ⊆ (G3s +
(□Cut))^⊗$ and $G3s^⊗ ⊆ (G3s + (Cut))^⊗$. Moreover $(G3s + (Cut))^⊗ ⊆
G3s^⊗$ by corollary \ref{boxcutloop} and $(G3s + (□Cut))^⊗ ⊆ (G3s +
(Cut))^⊗ ⊆ G3s^⊗$ by corollary \ref{cutloop}. All together we get:

$G3s^⊗ = (G3s + (Cut))^⊗ = (G3s + (□Cut))^⊗$
\End{proof}

Prehistoric relations and G3lp
==============================

The following is minimal subset of the Gentzen style system G3lp
without structural rules as introduced by @pulver2010 [62]. We do
replace the axioms (Axc) and (Axt) with rules $(⊃ :)_c$ and $(⊃ :)_t$
to keep to the prehistoric relations of the proof intact. As there is
a proof for $⊃ A$ for any axiom A and also for $A ⊃ A$ for any formula
A, this two rules are equivalent to the two axioms and invertible.
^[TODO more formal, relate to @pulver2010 65]

\renewcommand{\arraystretch}{3}
\begin{longtable}{cc}

\AXC{$P, Γ ⊃ Δ, P$ $(Ax)$ ($P$ atomic)}
\DP

&

\AXC{$⊥, Γ ⊃ Δ$ $(⊥⊃)$}
\DP

\\

\AXC{$⊃ A$}
\RightLabel{$(⊃ :)_c$ ($A$ an axiom of LP)}
\UIC{$Γ ⊃ Δ, c{:}A$}
\DP

&

\AXC{$t{:}A ⊃ A$}
\RightLabel{$(⊃ :)_t$}
\UIC{$t{:}A, Γ ⊃ Δ, t{:}A$}
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

\RightLabel{$(⊃ !)$}
\AXC{$Γ ⊃ Δ, t{:}A, !t{:}t{:}A$}
\UIC{$Γ ⊃ Δ, !t{:}t{:}A$}
\DP

\\

\RightLabel{$(⊃ +)$}
\AXC{$Γ ⊃ Δ, s{:}A, t{:}A, (s+t){:}A$}
\UIC{$Γ ⊃ Δ, (s+t){:}A$}
\DP

&

\RightLabel{$(⊃ ⋅)$}
\AXC{$Γ ⊃ Δ, s{:}(A → B), s⋅t{:}B$}
\AXC{$Γ ⊃ Δ, t{:}A, s⋅t{:}B$}
\BIC{$Γ ⊃ Δ, s⋅t{:}B$}
\DP

\end{longtable}

TODO repeat necessary results from @pulver2010

We expand the definition of correspondence \ref{corr} to G3lp proofs
in the natural way. That is, we consider all topmost proof terms in
active formulas in the rules $(⊃ ⋅)$, $(⊃ +)$ $(⊃ !)$ and $({:} ⊃)$ as
corresponding to each other. That leads to two main differences
between annotations for G3lp proofs and G3s proofs:

1. Families of proof terms in G3lp consist not of occurrences of a
single term $t$ but of occurrences of the set of subterms $s$ of a
term $t$ in the root sequent.

2. Similar to the cut rules in G3s, $(⊃ ⋅)$ relates subformulas and
symbols of different polarities.

So we will use the same approach as in the last chapter and use the
global definitions of prehistoric relations for all families where the
role of the $(⊃ □)$ rule is replaced by the $(⊃ :)$ rules as follows:

\Begin{definition}[Prehistoric Relation in G3lp] \label{g3lp}
A family $t_i$ has a *prehistoric relation* to another family $t_j$, in
notation $i ≺ j$, if there is a $(⊃ :)$ rule introducing an occurrence
of $t_j$ with premise $s$, such that there is an occurrence of $t_i$
in $T↾s$.^[TODO clearer and better definition and notation for families of terms]
\End{definition}

\Begin{lemma}
The forgetful projection of all rules in G3lp are admissible in G3s +
$(□Cut)$.
\End{lemma}

\Begin{proof}
The subset G3c is shared by G3lp and G3s and is therefore trivially
admissible. The forgetful projection of the rule $(⊃ +)$ is just a
contraction and therefore also admissible. The forgetful projection of
the rules $(⊃ :)_t$ and $(⊃ :)_c$ are $(⊃ □)$ rules in G3s.

We are left with the following two rules:

$(⊃ ⋅)$: The forgetful projection of a $(⊃ ⋅)$ rule is admissible by the
following derivation using a $(□Cut)$ and contraction:

\AXC{$Γ ⊃ Δ, □(A→B), □B$}
\AXC{$Γ ⊃ Δ, □(A), □B$}
\RightLabel{$(□Cut)$}
\BIC{$Γ ⊃ Δ, □B, □B$}
\DP

$(⊃ !)$: The forgetful projection of a $(⊃ !)$ rule has the following
form:

\AXC{$Γ ⊃ Δ, □A, □□A$}
\RightLabel{$(⊃ !)˚$}
\UIC{$Γ ⊃ Δ, □□A$}
\DP

This rule is admissible by lemma \ref{drop}.
\End{proof}

\Begin{lcorollary}
The forgetful projection of a G3lp proof has the same prehistoric
relations as the original G3lp proof. ^[TODO formulate one-way only or
actually proof that]
\End{lcorollary}

\Begin{proof}
As we replace $(⊃ :)$ rules directly with $(⊃ □)$ rules, the two
global definitions of prehistoric relations match. Moreover, all
contractions are on already related subformulas and $□$ symbols.  The
newly introduced $(□Cut)$ is also used on related $□$ symbols and
subformulas. So by corollaries \ref{contrprehist} and
\ref{dropprehist} as well as definition \ref{boxcutcorr}, no new
prehistoric relations are introduced in the forgetful projection.
\End{proof}

We will now come back to our example formula $¬□(P ∧ ¬□P)$ from
chapter \ref{self}. In figure \ref{g3lpproof} we see a proof of the
same realization $¬x{:}(P ∧ ¬t⋅x{:}P)$ in G3lp. For simplicity we will
just assume that $(A ∧ B → A)$ is an axiom A0 and therefore $t$ is a
proof constant. On the same figure we also included the forgetful
projection of that proof which is a G3s + $(□Cut)$ proof.

This proofs display the logical dependencies making the formula
self-referential in quite a different way than the original G3s proof
in figure \ref{proofs}. We have 3 families of $□$ in the G3s +
$(□Cut)$ proof. Two are the same families as in the G3s proof, and
have a consistent polarity throughout the proof. We therefore simply
use the symbols $⊞$ and $⊟$ for this families. The third one is part
of the cut formula and therefore does not occur in the final sequent
and does not have consistent polarity throughout the proof. We use $□$
for occurrences of this family in the proof.

All left prehistoric relations of the proof are from left branch of
the cut where we have $⊟ ≺_L ⊞$ and $⊞ ≺_L ⊞$. Other than in the G3s
proof, the two $⊞$ are used for different formulas $P$ and $P ∧ ¬□P$
and the connection between the two is established by the $(□Cut)$ with
$□(P ∧ ¬□P → P)$.

\afterpage{
\begin{landscape}
\begin{figure} \caption{G3lp proof} \label{g3lpproof}
\AXC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ P$}
\AXC{$P, t⋅x{:}P ⊃ P$}
\RightLabel{$(: ⊃)$}
\UIC{$t⋅x{:}P ⊃ P$}
\RightLabel{$(⊃ :)_t$}
\UIC{$P, t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ t⋅x{:}P$}
\RightLabel{$(⊃ ¬)$}
\UIC{$P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ t⋅x{:}P, ¬t⋅x{:}P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ ¬t⋅x{:}P$}
\RightLabel{$(⊃ ∧)$}
\BIC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ P ∧ ¬t⋅x{:}P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ P ∧ ¬t⋅x{:}P$}
\RightLabel{$(: ⊃)$}
\UIC{$x{:}(P ∧ ¬t⋅x{:}P) ⊃ P ∧ ¬t⋅x{:}P$}
\RightLabel{$(⊃ :)_t$}
\UIC{$P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ x{:}(P ∧ ¬t⋅x{:}P), t⋅x{:}P$}

\AXC{$P, ¬t⋅x{:}P ⊃ P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬t⋅x{:}P ⊃ P$}
\RightLabel{$(⊃ →)$}
\UIC{$ ⊃ P ∧ ¬t⋅x{:}P → P$}
\RightLabel{$(⊃ :)_c$}
\UIC{$P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ t{:}(P ∧ ¬t⋅x{:}P → P), t⋅x{:}P$}

\RightLabel{$(⊃ ⋅)$}
\BIC{$P, x{:}(P ∧ ¬t⋅x{:}P) ⊃ t⋅x{:}P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬t⋅x{:}P, x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(: ⊃)$}
\UIC{$x{:}(P ∧ ¬t⋅x{:}P) ⊃$}
\RightLabel{$(⊃ ¬)$}
\UIC{$⊃ ¬x{:}(P ∧ ¬t⋅x{:}P)$}
\DP

\AXC{$P, ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃ P$}
\AXC{$P, □P ⊃ P$}
\RightLabel{$(□ ⊃)$}
\UIC{$□P ⊃ P$}
\RightLabel{$(⊃ □)$}
\UIC{$P, □P, ⊟(P ∧ ¬⊞P) ⊃ ⊞P$}
\RightLabel{$(⊃ ¬)$}
\UIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞P, ¬□P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃ ¬□P$}
\RightLabel{$(⊃ ∧)$}
\BIC{$P, ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃ P ∧ ¬□P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃ P ∧ ¬□P$}
\RightLabel{$(□ ⊃)$}
\UIC{$⊟(P ∧ ¬⊞P) ⊃ P ∧ ¬□P$}
\RightLabel{$(⊃ □)$}
\UIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞(P ∧ ¬□P)$}

\AXC{$P, ¬□P ⊃ P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬□P ⊃ P$}
\RightLabel{$(⊃ →)$}
\UIC{$ ⊃ P ∧ ¬□P → P$}
\RightLabel{$(⊃ □)$}
\UIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞(P ∧ ¬□P → P)$}

\RightLabel{$(□Cut)$}
\BIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬⊞P, ⊟_0(P ∧ ¬⊞P) ⊃$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃$}
\RightLabel{$(□ ⊃)$}
\UIC{$⊟(P ∧ ¬⊞P) ⊃$}
\RightLabel{$(⊃ ¬)$}
\UIC{$⊃ ¬⊟(P ∧ ¬⊞P)$}
\DP
\end{figure}
\end{landscape}
}

Literature
==========

