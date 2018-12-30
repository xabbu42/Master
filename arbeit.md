---
title: Self-referentiality in Justification Logic
author: [Nathan Sebastian Gass]
date: "2019-01-01"
...

\begin{titlepage}
\begin{center}
\vspace*{1cm}

\Huge
\textbf{Self-referentiality in Justification Logic}

\vspace{0.5cm}
\LARGE
\textbf{Masterarbeit von\\Nathan Sebastian Gass\\}
\vspace*{0.5cm}
\Large
01. 01. 2019
\vfill
Foobar
\end{center}
\end{titlepage}

\tableofcontents

\newpage

Introduction
============

Sergei Artemov first introduced the Logic of Proofs $LP$ in
@artemov1995, where he introduced proof terms as explicit and
constructive replacements of the $□$ modality in S4.[^source] Later
more applications of this explicit notations were discovered for
different epistemic logics [@brezhnev2001]. So @artemov2008 introduced
the more general notion of justification logics, where justification
terms take over the role of the proof terms in $LP$. In any
justification logic, $t{:}A$ is read as $t$ is a justification of $A$,
leaving open what exactly that entails. Using different axioms and
different operators various different justification logic counterparts
where developed for the different modal systems used in epistemic
logic (K, T, K4, S4, K45, KD45, S5, etc.).

[^source]: Although @artemov1995 is the first comprehensive
presentation of the logic of proofs, this paper will mostly reference
and use the notations of the presentation in @artemov2001.

In justification logics it is possible for a proof term $t$ to be a
justification for a formula $A(t)$ containing $t$ itself, i.e. for the
assertion $t{:}A(t)$ to hold. Prima facie this seems suspicious from a
philosophical standpoint as well for more formal mathematical
reasons. Such a self-referential sentence is for example impossible
with an arithmetic proof predicate using standard Gödel numbers as the
Gödel number of a proof is always greater than any number referenced
in it as discussed in @kuznets2010. In the same paper, the author
argues that there is nothing inherently wrong with self-referential
justifications if we understand the justifications as valid reasoning
templates or schemes which of course then can be used on themselves.

Kuznets studied the topic of self-referentiality at the
logic-level. He discovered theorems of S4, D4, T and K4 which need a
self-referential constant specification to be realized in their
justification logic counterparts [@kuznets2010]. Yu on the other hand
studied self-referentiality at the theorem level. He discovered
prehistoric cycles as a necessary condition for self-referential S4
theorems in @yu2010 and later expanded that results to the modal
logics T and K4 in @yu2014. He also conjectured that the condition is
actually sufficient for self-referential S4 theorems. In this paper I
will concentrate on that topic, that is prehistoric cycles as
necessary and sufficient condition for self-referential theorems in
S4.

This paper is divided in three parts. In the first part I introduce
the modal logic S4 and its justification counterpart LP as well as two
Gentzen systems for S4 and LP used in the later parts. The second
part reproduces Yu's main theorem from @yu2010, that is, that
prehistoric cycles are a necessary condition for self-referential
theorems in S4. The third part goes beyond Yu's original paper by
adapting the notion of prehistoric cycles to Gentzen systems with cut
rules and finally to a Gentzen system for LP. This allows to study
prehistoric cycles directly in LP which leads to the two main results
of this paper. Firstly, with the standard definition of
self-referential theorems, prehistoric cycles are not a sufficient
condition. Second, with an expansion on the definition of
self-referential theorems, prehistoric cycles become sufficient
for self-referential theorems.

LP and S4
=========

Syntax
------

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
* $R2$: $A ⊢ c{:}A$, if $A$ is an axiom $A0-A4$ and $c$ a proof constant
        (Axiom Necessitation)

A Hilbert style derivation $d$ from a set of assumptions $Γ$ is a
sequence of formulas $A_0, ... A_n$ such that any formula is either an
instance of an axiom A0-A4, a formula $A ∈ Γ$ or derived from earlier
formulas by a rule R1 or R2. The notation $Γ ⊢_{LP} A$ means that a LP
derivation from assumptions $Γ$ ending in $A$ exists. We also write
$⊢_{LP} A$ or $LP ⊢ A$ if a LP derivation for $A$ without any assumptions
exists.

When formulating such derivations, we will introduce propositional
tautologies without derivation and use the term propositional
reasoning for any use of modus ponens together with a propositional
tautology. This is of course correct as axioms A0 together with the
modus ponens rule R1 are a complete Hilbert style system for classical
propositional logic. Its easy to see by a simple complete induction on
the proof length that this derivations do not use any new proof terms
not already occurring in the final propositional tautology.

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

1\.\ case: $B ≡ x_i{:}A_i$ is an assumption. Then $t := !x_i$ and $d'$
is the derivation $x_i{:}A_i$, $x_i{:}A_i → !x_i{:}x_i{:}A_i$,
$!x_i{:}x_i{:}A_i$.

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
the exact same axiom, if it already exists or else add the new
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
---------------------

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
system given by figure \ref{G3smin} using the standard derived
definitions for $¬$, $∨$, $∧$ and $◇$. All the missing rules from the
full system are admissible in the minimal system using this
definitions and the theorems therefore carry over to the full G3s
system.

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
absorbed.

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

\Begin{definition}[G3lift preproof]
A *G3lift preproof* is a proof tree using the rules of G3lift, but where
the (lift) rule may be used without fulfilling the necessary
precondition on the introduced term $t$.
\End{definition}

In all this rules, arbitrary formulas which occur in the premises and
the conclusion (denoted by repeated multisets $Γ$, $□Γ$, $Δ$ and $◇Δ$)
are called side formulas. Arbitrary formulas which only occur in the
conclusion (denoted by new multisets $Γ$, $Δ$, $Γ'$, $Δ'$) are called
weakening formulas.[^weak] The remaining single new formula in the conclusion
is called the principal formula of the rule. The remaining formulas in
the premises are called active formulas. Active formulas are always
used as subformulas of the principal formula. Active formulas which
are also strict subformulas of other active formulas of the same rule
as used in $(: ⊃)$ and $(□ ⊃)$ are contraction formulas.

[^weak]: Notice that weakening formulas only occur in axioms and the
rules $(⊃ □)$, $(◇ ⊃)$ and (lift), which are also the only rules which
restrict the possible side formulas.

Formally, a Gentzen style proof is denoted by $𝒯 = (T, R)$, where $T
:= \{S_0, ..., S_n\}$ is the set of occurrences of sequents, and $R :=
\{(S_i,S_j) ∈ T × T ∣ \text{$S_i$ is the conclusion of a rule which
has $S_j$ as a premise}\}$. The only root sequent of $𝒯$ is denoted by
$S_r$. A leaf sequent $S$ is a sequent without any premises, i.e $S
\slashed{R} S'$ for all $S' ∈ T$.

A path in a proof tree is a list of related sequent occurrences $S_0 R ... R
S_n$. A root path is a path starting at the root sequent
$S_r$. A root-leaf path is a root path ending in a leaf
sequent.[^treeterms] A root path is fully defined by the last sequent
$S$. So we will use root path $S$ to mean the unique path $S_r
R S_0 R ... R S$ from the root $S_r$ to the sequent $S$.
$T↾S$ denotes the subtree of $T$ with root $S$. The transitive closure
of $R$ is denoted by $R^+$ and the reflexive-transitive closure is
denoted by $R^*$.

[^treeterms]: Yu uses the term path for a root path and branch for a
root-leaf path. As this terminology is ambiguous we adopted the
slightly different terminology given here.

Consistent with the notation for the Hilbert style system LP, the
notation $G ⊢ Γ ⊂ Δ$ is used if there exists a Gentzen style proof
tree with the sequent $Γ ⊂ Δ$ as root in the system $G$.

\Begin{definition}[correspondence] \label{corr}
The subformula (symbol) occurrences in a proof correspond to each
other as follows:

* Every subformula (symbol) occurrence in a side formula of a premise
  directly corresponds to the same occurrence of that subformula
  (symbol) in the same side formula in the conclusion.

* Every active formula of a premise directly correspond to the topmost
  subformula occurrence of the same formula in the principal formula
  of the conclusion.

* Every subformula (symbol) occurrence in an active formula of a
  premise directly corresponds to the same occurrence of that
  subformula (symbol) in the corresponding subformula in the principal
  formula of the rule.

* Two subformulas (symbols) correspond to each other by the transitive
  reflexive closure of direct correspondence.

\End{definition}

As by definition correspondence is reflexive and transitive, we get
the following definition for the equivalence classes of correspondence:

\Begin{definition}[family]
A family is an equivalence class of symbol occurrences which respect
to correspondence.
\End{definition}

\Begin{theorem}[subformula property] \label{sub}
Any subformula (symbol) occurrence in a partial Gentzen style
(pre-)proof $T↾S$ in the systems G3lift and G3s corresponds to *at least
one* subformula (symbol) occurrence of the root sequent $S$ of $T↾S$.

Any subformula (symbol) occurrence in a complete Gentzen style
(pre-)proof $T$ in the systems G3lift and G3s corresponds to *exactly*
one subformula (symbol) occurrence in the root sequent $S_r$ of $T$.
\End{theorem}

\Begin{proof}
As defined, occurrences of subformulas only correspond directly via a
rule of the proof tree. Checking the rules of G3lift and G3s, we see
that each subformula occurrence in a premise always corresponds
directly to exactly one subformula occurrence in the conclusion.

So for any occurrence in the proof tree we get a unique path of
corresponding occurrences up to the root sequent of that tree, which
proofs the first part of the theorem. For the second part, notice that
two occurrences correspond indirectly if and only if their paths to
the root sequent merge at some point in the proof tree. So occurrences
in the root sequent itself can not correspond to each other.
\End{proof}

G3lift is sound and complete
----------------------------

We will show in this chapter that G3lift is adequate by showing it is
equivalent to the Hilbert system LP from @artemov2001 as introduced in
chapter \ref{syntax}.

\Begin{theorem}[Soundness of G3lift] \label{sound}
$\Glift ⊢ Γ ⊃ Δ ⇒ Γ ⊢_{LP} ⋁Δ$
\End{theorem}

\Begin{proof}
We construct a LP derivation $d$ of $⋁Δ$ by structural induction over
the proof tree $𝒯 = (T, R)$ for $Γ ⊃ Δ$.

1\.\ case: $Γ ⊃ Δ$ is an axiom $(Ax)$ with atomic formula $P$. Then it
has the form $P, Γ' ⊃ Δ', P$ and $P$, $P → ⋁Δ' ∨ P$, $⋁Δ' ∨ P$ is the
required LP derivation.

2\.\ case: $Γ ⊃ Δ$ is an axiom $(⊥ ⊃)$. Then it has the form $⊥, Γ' ⊃
Δ$ and $⊥$, $⊥ → ⋁Δ$, $⋁Δ$ is the required LP derivation.

3\.\ case: $Γ ⊃ Δ$ is derived by a $(→ ⊃)$ rule. Then it has the form
$A → B, Γ' ⊃ Δ$ and the the premises are $Γ' ⊃ Δ, A$ and $B, Γ' ⊃
Δ$. By the induction hypothesis there exists LP derivations $d_L$ and
$d_R$ for $Γ' ⊢_{LP} ⋁Δ ∨ A$ and $B, Γ' ⊢_{LP} ⋁Δ$. By the deduction
theorem (\ref{ded}) there exists a LP derivation $d_R'$ for $Γ' ⊢_{LP} B
→ ⋁Δ$. Using $d_R'$, the assumption $A → B$ and propositional
reasoning, we get $(A → B), Γ' ⊢_{LP} A → ⋁Δ$.  By appending $d_L$ and
propositional reasoning we get the final $(A → B), Γ' ⊢_{LP} ⋁Δ$

4\.\ case: $Γ ⊃ Δ$ is derived by a $(⊃ →)$ rule. Then it has the form
$Γ ⊃ Δ', A → B$ and the premise is $A, Γ ⊃ Δ', B$. By the induction
hypothesis there exists a LP derivation $d$ for $A, Γ ⊢_{LP} ⋁Δ' ∨
B$. From the deduction theorem (\ref{ded}) we get $Γ ⊢_{LP} A → (⋁Δ' ∨
B)$. By propositional reasoning we get the final $Γ ⊢_{LP} ⋁Δ' ∨ (A →
B) ≡ Γ ⊢_{LP} ⋁Δ$.

5\.\ case: $Γ ⊃ Δ$ is derived by a $(: ⊃)$ rule. Then it has the form
$t{:}A, Γ' ⊃ Δ$ and the premise is $A, t{:}A, Γ' ⊃ Δ$. By the
induction hypothesis there exists a LP derivation $d$ for $A, t{:}A,
Γ' ⊢_{LP} ⋁Δ$. By adding $t{:}A, t{:}A → A, A$ to the beginning of $d$
we get the necessary derivation $d'$ for $t{:}A, Γ' ⊢_{LP} ⋁Δ$.

6\.\ case: $Γ ⊃ Δ$ is is derived by a (lift) rule. Then it has the
form $t_1{:}A_1, ..., t_n{:}A_n ⊢_{LP} t{:}A$ and by the precondition
on $t$ there exists a derivation of $t_1{:}A_1, ..., t_n{:}A_n ⊢_{LP}
t{:}A$.
\End{proof}

\Begin{corollary} \label{soundvar}
The deduction $d$ for $Γ ⊢_{LP} ⋁Δ$ only uses variables $x$ which also
occur in the proof tree $𝒯 = (T, R)$ for $\Glift ⊢ Γ ⊃ Δ$ or any
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
the proofs for the same lemmas for G3s, as G3lift exactly mirrors
G3s. The only trivial difference is that the precondition of the
(lift) rule has to be checked whenever a different/new (lift) rule
gets introduced. Because of this and also because the following result
is just included for completeness and not actually used for the main
theorems of this text, we will omit the proofs here and refer the
reader to the proofs for G3s in @pulver2010 [40ff.] as well as later
in this text.

\Begin{lemma}[weakening for G3lift] \label{liftweak}
$\Glift ⊢ Γ ⊃ Δ ⇒ \Glift ⊢ Γ, Γ' ⊃ Δ, Δ'$
\End{lemma}

\Begin{lemma}[inversion for G3lift] \label{liftinverse}

* $\Glift ⊢ Γ ⊃ Δ, A → B ⇒ \Glift ⊢ A, Γ ⊃ Δ, B$

* $\Glift ⊢ A → B, Γ ⊃ Δ ⇒ \Glift ⊢ Γ ⊃ Δ, A \text{ and } \Glift ⊢ B, Γ ⊃ Δ$

* $\Glift ⊢ t:A, Γ ⊃ Δ ⇒ \Glift ⊢ A, t:A, Γ ⊃ Δ$

* $\Glift ⊢ Γ ⊃ Δ, t:A ⇒ \Glift ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{lemma}[contraction for G3lift] \label{liftcontr}

* $\Glift ⊢ A, A, Γ ⊃ Δ ⇒ \Glift ⊢ A, Γ ⊃ Δ$

* $\Glift ⊢ Γ ⊃ Δ, A, A ⇒ \Glift ⊢ Γ ⊃ Δ, A$

\End{lemma}

\Begin{lemma}[cut elimination for G3lift] \label{liftcut}
If $\Glift ⊢ A, Γ ⊃ Δ$ and $\Glift ⊢ Γ' ⊃ Δ', A$ then $\Glift ⊢ Γ,Γ' ⊃ Δ,Δ'$.
\End{lemma}

\Begin{lemma} \label{liftgenax}
$\Glift ⊢ A, Γ ⊃ Δ, A$ for any LP formula $A$.
\End{lemma}

\Begin{theorem}[Completeness of G3lift] \label{complete}
$Γ ⊢_{LP} A ⇒ \Glift ⊢ Γ ⊃ A$
\End{theorem}

\Begin{proof}
By complete induction over the length of the derivation $d$ for $Γ ⊢_{LP} A$.

1\.\ case $A$ is an axiom A0. By the completeness of G3c included in
G3lift there exists a derivation of $Γ ⊃ A$ and $⊃ A$ using the subset
G3c and lemma \ref{liftgenax} for the base cases.

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
--------------------------------

As we have already seen, all symbol occurrences in a Gentzen style
proof can be divided in disjoint equivalence classes of corresponding
symbol occurrences which are called families. In this text we will be
mainly concerned with the families of $□$ occurrences and their
polarities as defined below. We will therefore define annotated
formulas, sequents and proof trees in this chapter which make the
families and polarities of $□$ occurrences explicit in the notation
and usable in definitions.

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
for the derived operators all subformulas have the same polarity,
except for $¬$ which switches the polarity for its subformula.  ^[TODO
explain used syntax and equivalence or remove]

The rules of S4 respect the polarities of the subformulas, so that all
corresponding occurrences of subformulas have the same polarity
throughout the proof. We therefore assign positive polarity to
families of positive occurrences and negative polarity to families of
negative occurrences. Moreover, positive families in a S4 proof which
have occurrences introduced by a $(⊃ □)$ rule are called principal
positive families or simply principal families. The remaining
positive families are called non-principal positive families. [^essential]

[^essential]: This is the same terminology as used in @yu2010. In many
texts principal families are called essential families following the
original text [@artemov2001].

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

* If $A = □A_0$ and the $□$ belongs to a principal positive family
  $p_i$, then $an_T(A) := ⊞_i an_T(A_0)$.

* If $A = □A_0$ and the $□$ belongs to a non-principal positive family
  $o_i$, then $an_T(A) := ⊡_i an_T(A_0)$.

* If $A = □A_0$ and the $□$ belongs to a negative family $n_i$, then
  $an_T(A) := ⊟_i an_T(A_0)$.

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
-----------------------

LP and S4 are closely related and LP can be understood as an explicit
version of S4. The other way around, S4 can be seen as a version of LP
which proof details removed or forgotten. We will establish this close
relationship in this chapter formally by two main theorems
translating valid LP formulas into valid S4 formulas and vice
versa. The former is called forgetful projection, the latter is more
complex and called realization.

\Begin{definition}[forgetful projection] \label{proj}
The *forgetful projection* $A˚$ of a LP formula $A$ is the following S4 formula:

* if $A$ is atomic or $⊥$, then $A˚ := A$.
* if $A$ is the formula $A_0 → A_1$ then $A˚ := A_0˚ → A_1˚$
* if $A$ is the formula $t{:}A_0$ then $A˚ := □A_0$

The definition is expanded to sets, multisets and sequents of LP
formulas in the natural way.
\End{definition}

\Begin{theorem}
If $LP ⊢ A$ then $S4 ⊢ A˚$.
\End{theorem}

\Begin{proof}
If $LP ⊢ A$ then $\Glift ⊢ A$ with a proof tree $𝒯 = (T, R)$ by
completeness of G3lift (\ref{complete}). The forgetful projection of the
sequents of any G3lift rule map directly to the sequents of an
equivalent G3s rule, so the proof tree $𝒯' = (T˚, R)$ given by
replacing all sequents with the forgetful projection of that sequence
is a valid G3s proof with root sequent $⊃ A˚$. By the soundness of G3s
we have $S4 ⊢ A˚$.
\End{proof}

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
$r_A$ (respective a realization function $r_T$ relative to a proof
tree for $⊃ A$) and a constant specification of all constants
occurring in $r_A$ or $r_T$ with $A^r := r_A(an_A(A))$ respective $A^r
:= r_T(an_T(A))$.

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
$R_{i,0}, ... R_{i,l_i-1}$.  We will use $I_{i,0}, ... I_{i,l_i-1}$ to
denote the premises and $O_{i,0}, ... O_{i,l_i-1}$ to denote the
conclusions of this rules (so for all $i ≤ n_p$, $j < l_i$ we have
$I_{i,j}RO_{i,j}$). In total there are $N = Σ_{i = 0}^{n}l_i$ $(⊃
□)$ rules in the proof $T$.

We choose an order $ε(i,j) → \{1, ..., N\}$ of all the $(⊃
□)$ rules such that $ε(i_2,j_2) < ε(i_1,j_1)$ whenever
$O_{i_1,j_1}R^+O_{i_2,j_2}$ (i.e. rules closer to the root $s_r$ are
later in this order).

We define the normal realization function $r_T^0$ by $r_T^0(⊞_i) :=
u_{i,0} + ... + u_{i,l_i-1}$ and the injective constant specification
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
is also a correct G3lift proof. By soundness of G3lift (\ref{sound})
we therefore have a $LP(CS^{ε(i,j)-1})$ derivation for $r_T^{ε(i,j) -
1}(an_T(I_{i,j}))$, which has the following form:

\begin{equation} \label{start}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q} B_{k_q}) ⊢_{LP(CS^{ε(i,j) - 1})} r_T^{ε(i,j) - 1}(A)
\end{equation}

By the corollary \ref{liftcs} of the lifting lemma, we get a new proof
term $t_{i,j}(x_{k_0}, ..., x_{k_q})$ and a new injective
$CS'^{ε(i,j)} = CS^{ε(i,j) - 1} ∪ \{c_{i,j,0}{:}A_{i,j,0}, ...,
c_{i,j,m_{i,j}}{:}A_{i,j,m_{i,j}}\}$ such that:

\begin{equation} \label{lifted}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q} B_{k_q}) ⊢_{LP(CS'^{ε(i,j)})} t_{i,j}{:}r_T^{ε(i,j) - 1}(A)
\end{equation}

Define $r_T^{ε(i,j)}$ and $CS^{ε(i,j)}$ by replacing $u_{i,j}$ with
$t$ in $r_T^{ε(i,j) - 1}$ and $CS'^{ε(i,j)}$. By the substitution
lemma (\ref{subst}), the assertion \ref{lifted} still holds for
$r_T^{ε(i,j)}$ and $CS^{ε(i,j)}$. The formula $r_T^k(⊞_i A)$ has the
form $(s_0 + ··· +s_{j−1} + t_{i,j} + s_{j+1} + ··· +
s_{l_i-1}){:}A$. Therefore $LP_0 ⊢ t_{i,j}{:}A → r_T^k(⊞_i){:}A$ follows
from repeated use of $A4$. Together with the substituted \ref{lifted}
we get the precondition required for the final $(⊃ :)$ rule in
$r_T^{ε(i,j)}(an_T(T ↾ O_{i,j}))$:


\begin{equation} \label{precond}
r_T^{ε(i,j) - 1}(⊟_{k_0} B_{k_0}), ..., r_T^{ε(i,j) - 1}(⊟_{k_q}
B_{k_q}) ⊢_{LP(CS^{ε(i,j)})} r_T^{ε(i,j) - 1}(⊞_i A)
\end{equation}

Moreover, this precondition remains fulfilled for the $(⊃ :)$ rule
$R_{i,j}$ in any proof tree $r_T^k(an_T(T))$ for $k > ε(i,j)$ again by
the substitution lemma (\ref{subst}).

For the final normal realization function $r_T^N$ and injective
constant specification $CS^N$ we have that $r_T^N(an_T(T))$ is a
correct G3lift proof based on $CS^N$ of $⊃ r_T(A)$. So by soundness of
G3lift (\ref{sound}) we have $LP ⊢ A^r$ for the normal LP-realization
$r$ given by $r_T^N$ and the injective constant specification $CS^N$.
\End{proof}

\Begin{corollary} \label{realvar}
There exist derivations $d^k_{i,j}$ for the precondition
\ref{precond} of all rules $R_{i,j}$ in $r_T^k(an_T(T))$ and for any
$k ≥ ε(i,j)$ which do not introduce new variables.
\End{corollary}

\Begin{proof}
Proof by complete induction over the order $ε(i,j)$.  Given a rule
$R_{i,j}$, there exist derivations $d^k_{i_0,j_0}$ which do not
introduce new variables for the precondition of any rule $R_{i_0,j_0}$
in $r_T^k(an_T(T ↾ I_{i,j}))$ as $ε(i_0,j_0) < ε(i,j) ≤ k$ for all
this rules. Using the exact same steps as in the main proof but using
the realization function $r_T^k$, we get a derivation $d$ for
\ref{start} which does not introduce new variables by the corollary
\ref{soundvar}, a derivation $d'$ for \ref{lifted} which does not
introduce new variables by the corollary \ref{liftvar} and finally a
derivation $d^k_{i,j}$ for \ref{precond} which also does not introduce
new variables.
\End{proof}

Prehistoric Relations in S4
===========================

Self-referentiality
-------------------
\label{self}

As already mentioned in the introduction, the formulation of LP allows
for proof terms $t$ to justify formulas $A(t)$ about themselves. As we
will see such self-referential justification terms are unavoidable for
realizing S4 even at the basic level of justification constants. That
is to realize all S4 theorems in LP, we need self-referential constant
specifications defined as follows:

\Begin{definition}[self-referential constant specification]

* A constant specification $CS$ is *directly self-referential* if there is a
  constant $c$ such that $c{:}A(c) ∈ CS$.

* A constant specification $CS$ is *self-referential* if there is a
  subset $A ⊆ CS$ such that $A := \{c_0{:}A(c_1), ..., c_{n-1}{:}A(c_0)\}$.

\End{definition}

A constant specification which is not directly self-referential is
denoted by $CS^*$. Similarly a constant specification which is not
self-referential at all is denoted by $CS^⊛$. So $CS^*$ and $CS^⊛$
stand for a class of constant specifications and not a single specific
one. Following @yu2010, we will use the notation $LP(CS^⊛) ⊢ A$
if there exists any non-self-referential constant specification $CS$
such that $LP(CS) ⊢ B$. There does exist a single maximal constant
specification $CS_{nds}$ which is not directly self-referential and
for any theorem $A$ we have $LP(CS^*) ⊢ A$ iff $LP(CS_{nds}) ⊢ A$.

Given that any S4 theorem is realizable in LP with some constant
specification, we can carry over the definition of self-referentiality
to S4 with the following definition:

\Begin{definition}[self-referential theorem]
A S4 theorem $A$ is (directly) self-referential iff for any
LP-realization $A^r$ we have $LP(CS^⊛) \slashed{⊢} A^r$ (respective
$LP(CS^*) \slashed{⊢} A^r$).
\End{definition}

Expanding on a first result for S4 in @brezhnev2006 [31], @kuznets2010
[650] explores the topic of self-referentialiy on the level of
individual modal logics and their justicication counterparts. He gives
theorems for the modal logics S4, D4, T, and K4 which can only be
realized in their justification logic counterpart using directly
self-referential constant specifications, i.e. directly
self-referential theorems by the above definition. The example
directly self-referential theorem for S4 is $¬□¬(S → □S)$.

We will not reproduce this result but use the logicaly equivalent
formula $¬□(P ∧ ¬□P)$ as an example for a self-referential S4
theorem. Notice that it does not directly follow from the above
theorem that $¬□(P ∧ ¬□P)$ can only be realized with a
self-referential constant specification, as justification terms do not
necessary apply to logicaly equivalent formulas [@artemov2016 ch
1.3]. Still it should be fairly straightforward to show that $¬□(P ∧
¬□P)$ is self-referential by translating justification terms for the
outer $□$ occurrances in $¬□(P ∧ ¬□P)$ and $¬□¬(S → □S)$ using the
logical equivalence of $P ∧ ¬□P$ and $¬(S → □S)$.

The subformula $P ∧ ¬□P$ in our example asserts for an atomic sentence
$P$, for example "it will rain", to be true and unknown. This sentence
"It will rain and I do not know that it will rain" is inspired by
Moore's paradox and its formalization $P ∧ ¬□P$ is called a Moore
sentence. The sentence is easily satisfiable, for example if the
weather forecast wrongly predicts no rain, but it is impossible to now
that sentence, as is stated by our example theorem $¬□(P ∧
¬□P)$. Because if one knows the Moore sentence, one also knows the
first part of the conjunction, i.e.  $P$. This knowledge then
contradicts the second part of the conjunction,
$¬□P$. [cf. @artemov2016 ch 7]

Looking at the G3s proof for $¬□(P ∧ ¬□P)$ and a realization of that
proof in figure \ref{proofs}, we can see why a self referential proof
term like the used term $t$ for the propositional tautology $P ∧
¬t⋅x{:}P → P$ is necessary. In order to prove $¬□(P ∧ ¬□P)$ one needs
to disprove $P ∧ ¬□P$ at some point which means one has to prove
$□P$. The only way to prove $□P$ is using $□(P ∧ ¬□P)$ as an
assumption on the left. This leads to the situation that the proof
introduces $□$ by a $(⊃ □)$ rule where the same family already occurs
on the left. As the following sections of this chapter will show
formally such a situation is actually necessary for the
self-referentiality of an S4 formula.

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


Prehistoric Relations
---------------------

In his paper "Prehistoric Phenomena and Self-referentiality"
[@yu2010], Yu gave a formal definition for the situation described in
the last chapter, which he calls a prehistoric loop. In the later
paper @yu2017 he adopted the proper graph theoretic term cycle as we
do in this paper. Beside that change we will reproduce in this chapter
his definitions of prehistoric relation, prehistoric cycle as well as
some basic lemmas about this new notions exactly as they were presented
in the original paper.

\Begin{definition}[History]
In a root-leaf path $S$ of the form $S_rR^*O_{i,j}RI_{i,j}R^*S$ in a
G3s−proof $T$, the path $S_rR^*O_{i,j}$ is called a *history* of $p_i$
in the root-leaf path $S$. The path $I_{i,j}R^*S$ is called a
*pre-history* of $p_i$ in the root-leaf path $S$. ^[see @yu2010, 389]
\End{definition}

\Begin{definition}[Prehistoric Relation] \label{local1}
For any principal positive families $p_i$ and $p_h$ and any root-leaf path $S$ of
the form $S_rR^*O_{i,j}RI_{i,j}R∗S$ in a S4 proof $𝒯 = (T, R)$:

(1) If $an_T(I_{i,j})$ has the form $⊟_{k_0}B_{k_0}, ...,
⊟_{k}B_{k_q}(⊞_h C), ..., ⊟_{k_q}B_{k_q} ⊃ A$, then $p_h$ is a *left
prehistoric family* of $p_i$ in $S$ with notation $h ≺^S_L i$.

(2) If $an_T(I_{i,j})$ has the form $⊟_{k_0} B_{k_0} ∧ ... ∧
⊟_{k_q}B_{k_q} ⊃ A(⊞_h C)$ then $p_h$ is a *right prehistoric family*
of $p_i$ in $S$ with notation $h ≺^S_R i$.

(3) The relation of *prehistoric family* in $S$ is defined by: $≺^S := ≺^S_L ∪ ≺^S_R$.
The relation of *(left, right) prehistoric family* in $T$ is defined by:
$≺_L := ⋃\{≺^S_L |\text{$S$ is a leaf}\}$, $≺_R := ⋃\{≺^S_R |\text{$S$
is a leaf}\}$ and $≺ := ≺_L ∪ ≺_R$.

\End{definition}

The following lemma provides the connection between these two definitions:

\Begin{lemma} \label{global}
There is an occurrence of $⊞_h$ in a pre-history of $p_i$ in the root-leaf path
$S$ iff $h ≺^S i$.
\End{lemma}

\Begin{proof}
(⇒): $⊞_h$ occurs in a sequent $S'$ in a pre-history of $p_i$ in the
root-leaf path $S$, so $S$ has the form
$S_rR^*O_{i,j}RI_{i,j}R^*S'R^*S$ for some $j < l_i$. By the subformula
theorem \ref{sub}, there is an occurrence of $⊞_h$ in $I_{i,j}$ as
$S'$ is part of $T↾I_{i,j}$. If this occurrence is on the left we have
$h ≺^S_L i$, if it is on right we have $h ≺^S_R i$. In both cases $h
≺^S i$ holds.

(⇐): By definition there is a $I_{i,j}$ in $S$, where $⊞_h$ occurs
either on the left (for $h ≺^S_L i$) or on the right (for $h ≺^S_R
i$). $I_{i,j}$ is part of the pre-history of $R_{i,j}$ in $S$.
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
If $k ≺_R j$ and $j ▹ i$, then $k ▹ i$, where $▹$ is any one of $≺$,
$≺_L$, $≺_R$, $≺^s$ , $≺^s_L$ or $≺^s_R$.
\End{lemma}

\Begin{proof}
Since $k ≺_R j$, there is a $⊞_k$ occurring in the scope of a
principally introduced $⊞_j$. All corresponding occurrences of $⊞_j$
are part of corresponding occurrences of the subformula $⊞_jA(⊞_kB)$,
with exactly one occurrence in the root sequent $S_r$ by the
subformula property \ref{sub}. So wherever $⊞_j$ occurs in the proof
$T$, there is a $⊞_k$ occurring in the scope of it.

For any $▹$, we have $j ▹ i$ because some occurrence of $⊞_j$ in a
subformula of the premise of a rule $R_{i,q}$. By the previous
statement there is also an occurrence of $⊞_k$ in the same scope, and
therefore also $k ▹ i$.
\End{proof}

\Begin{definition}[Prehistoric Cycle]
In a G3s−proof $T$, the ordered list of principal positive families
$p_{i_0},..., p_{i_{n-1}}$ with length $n$ is called a *prehistoric cycle* or *left
prehistoric cycle* respectively, if we have: $i_0 ≺ i_2 ≺ ... ≺ i_{n-1} ≺
i_0$ or $i_0 ≺_L i_2 ≺_L ... ≺_L i_{n-1} ≺_L i_0$.
\End{definition}

\Begin{lemma}
$T$ has a prehistoric cycle iff $T$ has a left prehistoric cycle.
\End{lemma}

\Begin{proof}
The (⇐) direction is trivial. The (⇒) direction is proven by complete
induction on the length of the cycle as follow:

$n = 1$: $i_0 ≺ i_0$ so either $i_0 ≺_R i_0$ or $i_0 ≺_L i_0$. As $i_0
≺_R i_0$ is impossible by lemma \ref{noref}, we have $i_0 ≺_L i_0$ and the
cycle already is a left prehistoric cycle.

$n - 1 ⇒ n$: If $i_k ≺_L i_{k+1 \mod n}$ for all $k < n$, then the
cycle already is a left prehistoric cycle and we are finished. Otherwise
there is a $k < n$ such that $i_k ≺_R i_{k+1 \mod n} ≺ i_{k+2 \mod
n}$. By lemma \ref{trans} we also have $i_k ≺ i_{k+2 \mod n}$ and
therefore the sublist of length $n - 1$ without $i_{k+1 \mod n}$ is
also a prehistoric cycle. By the induction hypothesis, $T$ has a left
prehistoric cycle.
\End{proof}


Main Proof
----------

Yu's proof for the main theorem of his paper, builds upon the idea to
carefully choose the order $ε(i,j)$ used in the realization theorem
(\ref{realization}), such hat the generated constant specifications
$CS^{ε(i,j)}$ never contain any provisional variables $u_{x,y}$. With
such an order, formulas $c{:}A_{i,j,k}$ introduced during the
realization procedure never change after their introduction, and we
get a strong limitation of the proof constants which can occur in such
a formula. This limitation finally will show that the generated CS using
that order can not be self-referential.

\Begin{lemma} \label{variablefree}
Any provisional variable $u_{x,y}$, which does not occur in
$r^{ε(i,j) - 1}(an_T(I_{i,j}))$, does not occur in $CS^{ε(i,j)}$.
\End{lemma}

\Begin{proof}
By the subformula property (\ref{sub}) for G3lift proofs, $u_{x,y}$
does not occur in $r^{ε(i,j)−1}(an_T(T↾I_{i,j}))$. By the corollary
\ref{soundvar} using corollary \ref{realvar} for case 6, the
derivation $d_{i,j}$ as constructed in the realization proof does not
contain $u_{x,y}$. By the corollary \ref{liftvar} of the lifting
theorem, $CS'_{i,j}$ and $t_{i,j}$ do not contain $u_{x,y}$. So also
$CS_{i,j}$ constructed by a substitution of $u_{i,j}$ with $t_{i,j}$
does not contain $u_{x,y}$.
\End{proof}

\Begin{lemma} \label{epsilon}
If a G3s−proof $T$ is prehistoric-cycle-free, then we can realize it in
such a way that: If $h_2 ≺ h_1$, then $ε(h_2,j_2) < ε(h_1,j_1)$ for any
$j_1 < l_{h_1}$ and $j_2 < l_{h_2}$.
\End{lemma}

\Begin{proof}
For a prehistoric-cycle-free proof $T$, $≺$ describes a directed
acyclic graph. Therefore there exists a topological order
$p_{k_0},...,p_{k_{n_p}}$ of the $n_p + 1$ principal positive families
$p_0, ..., p_{n_p}$. For any root-leaf path $S$ of the form
$S_rR^*O_{i_1,j_1}R^+O_{i_2,j_2}R^*S$, we have $i_2 ≺ i_1$ by lemma
\ref{global}. So the order $ε(k_x,j) := j + Σ_{w = 0}^{x-1}l_{k_w}$
defined for each family $p_{k_x}$ and each $j < l_{k_x}$ by handling the
families $p_i$ in the given topological order $k_x$ fulfills the
necessary condition to be used in the realization theorem
\ref{realization} and at the same time the condition given in this
lemma.
\End{proof}

\Begin{lemma} \label{constants}
Assume the proof tree is prehistoric-cycle-free. Taken the $ε$ as
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
ε(i,j)$ for all $j_h < l_h$. So any provisional variable $u_{h,j_h}$
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

\Begin{theorem}[Necessity of Left Prehistoric Cycle for Self-referentiality]
If a S4−theorem $A$ has a left-prehistoric-cycle-free G3s−proof, then
there is a LP−formula $B$ s.t. $B^◦ = A$ and $LP(CS^⊛) ⊢ B$
\End{theorem}

\Begin{proof}
Given a left-prehistoric-cycle-free G3s−proof $T$ for $A$, use lemma
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
$CS^N$ is not self-referential and we have $LP(CS^⊛) ⊢ B$.
\End{proof}

Prehistoric Relations in LP
===========================

Prehistoric relations in G3s with cut rules
-------------------------------------------

In this chapter we will define prehistoric relations in the systems
G3s + (Cut) and G3s + (□Cut). The (context sharing) cut rule has the
following definition [@troelstra2000 67]:

\Begin{definition}[(Cut) rule]

\AXC{$Γ ⊃ Δ, A$}
\AXC{$A, Γ ⊃ Δ$}
\RightLabel{(Cut)}
\BIC{$Γ ⊃ Δ$}
\DP

\End{definition}

It is necessary to expand the definition of correspondence
(\ref{corr}) to (Cut) rules as follows:

\Begin{definition}[correspondence for (Cut)]

* The active formulas (and their symbols) in the premises of a (Cut) rule correspond
to each other.

\End{definition}

The classification and annotations for families of $□$ do not carry
over to G3s + (Cut), as the (Cut) rule uses the cut formula in
different polarities for the two premises. We therefore will consider
*all* $□$ families for prehistoric relations in G3s + (Cut) proofs.
This leads to the following expanded definition of prehistoric relation:

\Begin{definition}[Local Prehistoric Relation in G3s + (Cut)] \label{local2}
A family $□_i$ has a *prehistoric relation* to another family $□_j$, in
notation $i ≺ j$, if there is a $(⊃ □)$ rule introducing an occurrence
of $□_j$ with premise $S$, such that there is an occurrence of $□_i$
in $S$.
\End{definition}

Notice that there can be prehistoric relations with $□$ families which
locally have negative polarity, as the family could be part of a cut
formula and therefore also occur with positive polarity in the other
branch of the cut. On the other hand, adding prehistoric relations
with negative families in a cut free G3s proof does not introduce
prehistoric cycles, as in G3s a negative family is never introduced by
a $(⊃ □)$ rule and therefore has no prehistoric families itself. In
G3s + (Cut) proofs, the subformula property (\ref{sub}) and
therefore also lemma \ref{global} no longer holds. That means we can
have an occurrence of a family $□$ as part of a cut formula in the
*global* prehistory of a $(⊃ □)$ rule, which by the *local* definition
\label{defcut} is not a local prehistoric family.

To handle proof terms $s⋅t$ in the next chapter an additional rule for
modus ponens under $□$ is necessary. We therefore introduce here the new rule
(□Cut) as follows:

\Begin{definition}[(□Cut) rule]

\AXC{$Γ ⊃ Δ, □A, □B$}
\AXC{$Γ ⊃ Δ, □(A → B), □B$}
\RightLabel{(□Cut)}
\BIC{$Γ ⊃ Δ, □B$}
\DP

\End{definition}

Again it is also necessary to expand the definition of correspondence
(\ref{corr}) for this rule:

\Begin{definition}[correspondence for (□Cut)] \label{boxcutcorr}

* The topmost $□$ occurrence in the active formulas and the principal
  formula correspond to each other.

* The subformulas $A$ in the active formulas of the premises correspond
  to each other.

* The subformulas $B$ correspond to each other.

\End{definition}

Notice that with this expansion, $□$ occurrences of the same family no
longer are always part of the same subformula $□C$ and therefor lemma
\ref{trans} no longer holds.^[TODO make sure] Also similar to the
(Cut) rule, correspondence is expanded to relate negative and positive
occurrences of $□$ symbols.

With the following lemmas and theorems we will establish a
constructive proof for $\Gs + (□\Cut) ⊢ Γ ⊃ Δ ⇒ \Gs + (\Cut) ⊢ Γ ⊃ Δ ⇒
\Gs ⊢ Γ ⊃ Δ$. Moreover there will be corollaries showing that the
constructions do not introduce prehistoric cycles by the new definition
\ref{local2}. As all prehistoric relations by the first definition
\ref{local1} are included in the new definition, the final proof in
G3s will be prehistoric-cycle-free by any definition if the original
proof G3s + (□Cut) was prehistoric-cycle-free by the new definition.

It is important to note, that all the following corollaries are not
restricted to the annotations $an_T$ of the proofs $𝒯 = (T, R)$ given
by the premise of the lemma but still hold for arbitrary annotations
$an$. That means there is no implicit assumption that the families
have only a single occurrence in the root sequents used in the lemma or theorem
and the results can also be used in subtrees $T↾S$ together with an
annotation $an_T$ for the complete tree.

\Begin{lemma}[weakening for G3s] \label{weak}
$\Gs ⊢ Γ ⊃ Δ ⇒ \Gs ⊢ Γ, Γ' ⊃ Δ, Δ'$
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
For any annotation $an$ the proof for $\Gs ⊢ Γ, Γ' ⊃ Δ, Δ'$ as
constructed in the main proof has the exact same prehistoric relations
as the original proof for $\Gs ⊢ Γ ⊃ Δ$.
\End{lcorollary}

The last corollary also follows from the fact 2.8 in @yu2017 [787]. In
that paper Yu looks at prehistoric relations localy, i.e. taking only
correspondence up to the current sequent in consideration. That means
the graph of prehistoric relations has to be updated going up the
proof tree as new rules add new correspondences and therefore unify
vertices in the prehistoric relations graph which were still seperate
in the premise. To work with such changing graphs, Yu introduces the
notion of isolated families. He shows that all $□$ occurrences
introduced by weakening are isolated. That means they have no
prehistoric relations themself, which globaly means that they can not
add any prehistoric relations from adding correspondences later in the
proof. This is exactly what the last corollary asserts.

\Begin{proof}
$(⊃ □)$ rules are handled by the 3\.\ case by new $(⊃ □)$ rules that
use the exact same premise and only in the history add the new
weakening formulas. So all prehistoric paths are unchanged and all
prehistoric relations remain the same.
\End{proof}

\Begin{lemma}[inversion for G3s] \label{invers}

* $\Gs ⊢ Γ ⊃ Δ, A → B ⇒ \Gs ⊢ A, Γ ⊃ Δ, B$

* $\Gs ⊢ A → B, Γ ⊃ Δ ⇒ \Gs ⊢ Γ ⊃ Δ, A \text{ and } \Gs ⊢ B, Γ ⊃ Δ$

* $\Gs ⊢ □A, Γ ⊃ Δ ⇒ \Gs ⊢ A, □A, Γ ⊃ Δ$

* $\Gs ⊢ Γ ⊃ Δ, □A ⇒ \Gs ⊢ Γ ⊃ Δ, A$

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
In the 1.\ case and 2.\ case we only remove occurrences of $□$ so no
new prehistoric relations are introduced. In the 3\.\ case, a rule is
removed entirely, which again can not introduce new prehistoric
relations.
\End{proof}

\Begin{lemma}[contraction for G3s] \label{contr}

* $\Gs ⊢ A, A, Γ ⊃ Δ ⇒ \Gs ⊢ A, Γ ⊃ Δ$

* $\Gs ⊢ Γ ⊃ Δ, A, A ⇒ \Gs ⊢ Γ ⊃ Δ, A$

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

\Begin{proof}
In the 1\. case and 2\. case we only remove occurrences of $□$ so no
new prehistoric relations are introduced. In the 3\.\ case, by
corollary \ref{inversprehist} no new prehistoric relations are
introduced for the new proof where both occurrences of $A$ are
deconstructed. Moreover, in the case of appending a $(⊃ □)$ rule, all
occurrences in the new premise are also in the old premise and therefore
no new prehistoric relations get introduced.
\End{proof}

\Begin{lemma} \label{drop}
$\Gs ⊢ B, □B, Γ ⊃ Δ ⇔ \Gs ⊢ B, Γ ⊃ Δ$
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
If $\Gs ⊢ Γ ⊃ Δ, A$ and $\Gs ⊢ A, Γ ⊃ Δ$ then $\Gs ⊢ Γ ⊃ Δ$.
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
proofs. We distinguish the following subcases:

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

\RightLabel{(Cut)}
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

\RightLabel{(Cut)}
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

\RightLabel{(Cut)}
\BIC{$Γ ⊃ Δ$}
\DP

Using weakening and two cuts with the lower rank formulas $A_0$ and $A_1$ we can
transform that into:

\AXC{$𝒯'_{R1}$} \noLine
\UIC{$Γ ⊃ Δ, A_1, A_0$}
\AXC{$𝒯_L$} \noLine
\UIC{$A_0, Γ ⊃ Δ, A_1$}
\RightLabel{(Cut)}
\BIC{$Γ ⊃ Δ, A_1$}
\AXC{$𝒯_{R2}$} \noLine
\UIC{$A_1, Γ ⊃ Δ$}
\RightLabel{(Cut)}
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

\RightLabel{(Cut)}
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
\RightLabel{(Cut)}
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
the new $(⊃ □)$ in case 2.3. All prehistoric relations from $□Γ_R$ are
already present from the $(⊃ □)$ rule on the right in the original
proof. So only prehistoric relations from $□Γ_L$ are new. For all
families $□_i$ in $□Γ_L$ we have $i ≺ k$ for the family $□_k$ in the
cut formula introduced by the $(⊃ □)$ rule on the left. Moreover $k ≺
j$ for the same family because of the occurrence of $□A_0$ on the
right.
\End{proof}

\Begin{corollary} \label{cutcycle}
For any annotation $an$ the constructed proof for $Γ ⊃ Δ$ does not
introduce prehistoric cycles.
\End{corollary}

\Begin{proof}
Assume for contradiction that there exists a prehistoric cycle $i_0 ≺
... ≺ i_{n-1} ≺ i_0$ in the new proof. By the previous lemma for any
prehistoric relation $i_k ≺ i_{k+1 \mod n}$ in the cycle either $i_k ≺
i_{k+1 \mod n}$ in the original proof or there is a family $i'_k$ in
the cut formula such that $i_k ≺ i'_k ≺ i_{k+1 \mod n}$ in the
original proof. Therefore we also have a prehistoric cycle in the
original proof.
\End{proof}

\Begin{theorem}[(□Cut) elimination] \label{boxcut}
If $\Gs ⊢ Γ ⊃ Δ, □A, □B$ and $\Gs ⊢ Γ ⊃ Δ, □(A → B), □B$ then $\Gs ⊢ Γ ⊃ Δ, □B$
\End{theorem}

\Begin{proof}
By a structural induction over the proof trees $𝒯_L$ for
$Γ ⊃ Δ, □A, □B$ and $𝒯_R$ for $Γ ⊃ Δ, □(A → B), □B$.

1\.\ case: $□(A → B)$ or $□A$ is a weakening formula of the last
rule. Then removing them from that proof gives the required
proof. This includes the case when $□B$ is the principal formula of
the last rule of either proof, as then the last rule is $(⊃ □)$ which
has no side formulas on the right.

2\.\ case: $□(A → B)$ or $□A$ is a side formula of the last rule. Then
also $□B$ is a side formula of that rule.  Use the induction
hypothesis on the premises of that rule with the other proof and
append the same rule.

3\.\ case: $□(A → B)$ and $□A$ are the principal formula of the last
rule. Then the last rules have the following form:

\AXC{$𝒯_L$} \noLine
\UIC{$□Γ_L ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ_L', □Γ_L  ⊃ Δ, □A, □B$}

\AXC{$𝒯_R$} \noLine
\UIC{$□Γ_R ⊃ A → B$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ'_R, □Γ_R  ⊃ Δ, □(A → B), □B$}

\RightLabel{(□Cut)}
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
\RightLabel{(Cut)}
\BIC{$□Γ_L, □Γ_R ⊃ B$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ, □Γ_L, □Γ_R ⊃ Δ, □B$}
\DP

By contraction and a cut elimination we get the required G3s proof for
$Γ ⊃ Δ, □B$ as $□Γ_L ⊆ Γ$ and $□Γ_R ⊆ Γ$.
\End{proof}

\Begin{corollary} \label{boxcutcycle}
For any annotation $an$ the constructed proof for $Γ ⊃ Δ, □B$ does not
introduce prehistoric cycles.
\End{corollary}

\Begin{proof}
Removing weakening or side formulas $□(A→B)$ or $□A$ as in case 1 and
2 does not introduce new prehistoric relations.

Any prehistoric relation because of the new $(⊃ □)$ rule in case 3
already exists in the original proof, as every $□$ occurrence in
$□Γ_L$ or $□Γ_R$ also occurs in one of the two $(⊃ □)$ rules in the
original proof, which both introduce a □ of the same family as $□B$
by the definition of correspondence for (□Cut) (\ref{boxcutcorr}).

So the new proof with (□Cut) rules replaced by (Cut) rules does
not introduce new prehistoric relations and therefore also no new
prehistoric cycles. By corollary \ref{cutcycle}, the cut elimination to
get a G3s proof does not introduce prehistoric cycles.
\End{proof}

\Begin{definition}
The cycle-free fragment of a system $Y$, denoted by $Y^⊗$, is the
collection of all sequents that each has a prehistoric-cycle-free
$Y$-proof [@yu2017 787].
\End{definition}

\Begin{theorem}
The cycle-free fragments of G3s + (□Cut), G3s + (Cut) and G3s are
identical.
\End{theorem}

\Begin{proof}

A prehistoric-cycle-free proof in G3s by the original definition
(\ref{local1}) is also prehistoric-cycle-free by the new definition
(\ref{local2}) as a negative family can not have any prehistoric
families itself in a G3s-proof . So any sequent $Γ ⊂ Δ ∈ G3s^⊗$ is
trivially also provable prehistoric-cycle-free in G3s + (Cut) and G3s
+ (□Cut) and we have $\Gs^⊗ ⊆ (\Gs + (□\Cut))^⊗$ and $\Gs^⊗ ⊆ (\Gs +
(\Cut))^⊗$. Moreover $(\Gs + (\Cut))^⊗ ⊆ \Gs^⊗$ by corollary
\ref{cutcycle} and $(\Gs + (□\Cut))^⊗ ⊆ (\Gs + (\Cut))^⊗ ⊆ \Gs^⊗$ by
corollary \ref{boxcutcycle}. All together we get:

$\Gs^⊗ = (\Gs + (\Cut))^⊗ = (\Gs + (□\Cut))^⊗$
\End{proof}

In the theorem 2.21 [@yu2017 793], Yu shows that
non-self-referentiality is not normal in T, K4 and S4. The results in
this chapter hint at an explanation for this fact for S4 and at the
possibility to still use modus ponens with further restrictions in the
non-self-referential subset of S4. Namely, to consider the global
aspects of self-referentiality coming from correspondence of
occurrences, it is necessary when combining two proofs to get a new
proof, that the two proofs combined with the correct correspondences
added are prehistoric-cycle-free. So we can only use modus ponens on
two non-self-referential S4 theorems $A$ and $A → B$ if there are
proofs of $A$ and $A → B$ such that the prehistoric relations of these
proofs combined together with identifing the occurrences of $A$ in
both proofs are prehistoric-cycle-free. In that case we get a
prehistoric-cycle-free G3s proof for $B$ using cut elimination and
corollary \ref{cutprehist}, which shows that $B$ is
non-self-referential.

Prehistoric relations and G3lp
------------------------------

@pulver2010 [62] introduces the system LPG3 by expanding G3c with
rules for the build up of proof terms with build in contraction as
well as the new axioms (Axc) and (Axt). We will in our variant of G3lp
use the same rules to build up proof terms, but replace the axioms
with rules $(⊃ :)_c$ and $(⊃ :)_t$ to keep the prehistoric relations
of the proof intact. As there is a proof for $⊃ A$ for any axiom $A$ and
also for $A ⊃ A$ for any formula $A$, this two rules are equivalent to
the two axioms and invertible.

As we already did with G3s, we will use the full system with all
classical operators for examples, but only the minimal subset with $→$
and $⊥$ for proofs. So this two systems use the classical rules from
G3s in figure \ref{G3sfull} and \ref{G3smin} as well as the new LP
rules in figure \ref{G3lprules}.

\renewcommand{\arraystretch}{3}
\begin{figure} \caption{G3lp} \label{G3lprules}
\begin{longtable}{cc}

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
\end{figure}

TODO repeat necessary results from @pulver2010

\Begin{definition}[subterm]
The set of subterms $\sub(t)$ of a LP proof term $t$ is inductively defined as
follows:

1. $\sub(x) = \{x\}$ for any proof variable $x$
2. $\sub(c) = \{c\}$ for any proof constant $c$
3. $\sub(!t) = \sub(t) ∪ \{!t\}$
4. $\sub(s+t) = \sub(s) ∪ \sub(t) ∪ \{s + t\}$
5. $\sub(s⋅t) = \sub(s) ∪ \sub(t) ∪ \{s⋅t\}$

\End{definition}

\Begin{definition}[subformula]
The set of subformulas $\sub(A)$ of a LP formula $A$ is inductively defined as follows:

1. $\sub(P) = \{P\}$ for any atomic formula $P$
2. $\sub(⊥) = \{⊥\}$
3. $\sub(A_0 → A_1) = \sub(A_0) ∪ \sub(A_1) ∪ \{A_0 → A_1\}$
4. $\sub(s+t{:}A_0) = \sub(A_0) ∪ \{s{:}A_0, t{:}A_0, s+t{:}A_0\}$
5. $\sub(t{:}A_0) = \sub(A_0) ∪ \{t{:}A_0\}$

\End{definition}

\Begin{definition}[subterms of a formula]
The set of subterms $\sub(A)$ of a LP formula $A$ is the union of all
sets of subterms of any term occurring in $A$.
\End{definition}

We use $\sub$ for all three definitions, as it will be clear from
context which of the three definitions is meant.  Notice that by this
definition $s{:}A$ is a subformula of $s+t{:}A$.

We adapt the definition of correspondence (\ref{corr}) to G3lp proofs
as follows: all topmost proof terms in active or principal formulas in
the rules $(⊃ ⋅)$, $(⊃ +)$ $(⊃ !)$ and $({:} ⊃)$ correspond to each
other. Notice that in the $(⊃ !)$ rule, the topmost proof term $t$
in the contraction formula therefore corresponds to the topmost proof
term $!t$ in the principal formula. The proof term $t$ of the other
active formula $!t:t:A$ on the other hand corresponds to the same
proof therm $t$ in the principal formula.

By this definition, families of proof terms in G3lp consist not of
occurrences of a single term $t$ but of occurrences of subterms $s$ of
a top level term $t$.  We will use $\bar{t}$ for the family of
occurrences corresponding to the *top level* term $t$, i.e. seen as a
set of terms instead of term occurrences we have $\bar{t} ⊆
\sub(t)$. So for any term occurrence $s$, $\bar{s}$ is not necessarily
the full family of $s$ in the complete proof tree as $s$ could be a
subterm of the top level term $t$ of the family. For any occurrence
$s$ in a sequent $S$ of the proof tree though, $\bar{s}$ is the family
of $s$ relative to the subtree $T↾S$ as all related proof terms in the
premises of G3lp rules are subterms of the related proof term in the
conclusion.

We also see that most rules of G3lp only relate proof terms to each
other used for the same subformula $A$. The two exceptions are the $(⊃
⋅)$ rule and the $(⊃ !)$ rule. Similar to the cut rules from the
previous chapter, $(⊃ ⋅)$ relates subformulas and symbols of different
polarities as well as terms used for different formulas. So we will
use the same approach as in the last chapter to define prehistoric
relations of proof term families for any polarity:

\Begin{definition}[Prehistoric Relation in G3lp] \label{g3lp}
A family $\bar{t_i}$ has a *prehistoric relation* to another family $\bar{t_j}$, in
notation $i ≺ j$, if there is a $(⊃ :)$ rule introducing an occurrence
of $\bar{t_j}$ with premise $S$, such that there is an occurrence of $\bar{t_i}$
in $S$.
\End{definition}

Given that we now have defined families of terms and prehistoric
relations between them in G3lp, it is interesting to see what happens
with this relations if we look at the forgetful projection of a G3lp
proof. That is, what happens on the G3s side if we construct a proof
tree with the forgetful projections of the original sequents. Of
course we do not get a pure G3s proof as most of the G3lp rules have
no direct equivalent in G3s.  We will therefore introduce new rules,
which are the forgetful projection of a G3lp rule denoted for example
by $(⊃ !)˚$ for the forgetful projection of a $(⊃ !)$ rule. The
following two lemmas show that all new rules are admissible in G3s +
$(□\Cut)$.

\Begin{lemma} \label{boxbox}
$\Glp ⊢ Γ ⊃ Δ, □A$ iff $\Glp ⊢ Γ ⊃ Δ, □□A$.
\End{lemma}

\Begin{proof}
The (⇐) direction is just inversion for $(⊃ □)$. The (⇒) direction
is proven by the following structural induction:

1\.\ case: $□A$ is a weakening formula of the last rule. Just weaken
in $□□A$.

2\.\ case: $□A$ is a side formula of the last rule. Use the induction
hypothesis on the premises and append the same last rule.

3\.\ case: $□A$ is the principal formula of the last rule. Then the
last rule is a $(⊃ □)$ rule and has the following form:

\AXC{$□Γ ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ', □Γ ⊃ Δ, □A$}
\DP

Use an additional $(⊃ □)$ rule to get the necessary proof as follows:

\AXC{$□Γ ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$□Γ ⊃ □A$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ', □Γ ⊃ Δ, □□A$}
\DP
\End{proof}

\Begin{lemma}
The forgetful projection of all rules in G3lp are admissible in G3s +
(□Cut).
\End{lemma}

\Begin{proof}
The subset G3c is shared by G3lp and G3s and is therefore trivially
admissible. The forgetful projection of the rule $(⊃ +)$ is just a
contraction and therefore also admissible. The forgetful projection of
the rules $(⊃ :)_t$ and $(⊃ :)_c$ are $(⊃ □)$ rules in G3s. The
forgetful projection of $(⊃ ⋅)$ is a $(□\Cut)$. Finally the forgetful
projection of a $(⊃ !)$ rule has the following form:

\AXC{$Γ ⊃ Δ, □A, □□A$}
\RightLabel{$(⊃ !)˚$}
\UIC{$Γ ⊃ Δ, □□A$}
\DP

That rule is admissible by lemma \ref{boxbox} and a contraction.
\End{proof}

Instead of working with a G3s system with all this extra rules
included, we will define a forgetful projection from a G3lp proof to a
G3s + $(□\Cut)$ proof by eliminating all the contractions using the
algorithm implicitly defined in the proof of the contraction lemma
(\ref{contr}) and eliminating the $(⊃ !)˚$ rules by the algorithm
implicitly described in the proof for lemma \ref{boxbox}.

For the following lemmas and proofs we fix an arbitrary G3lp proof $𝒯 =
(T, R)$ and its forgetful projection $𝒯˚ = (T', R')$ as defined
below.

\Begin{definition}[forgetful projection of a G3lp proof]
The forgetful projection of a G3lp proof $𝒯 = (T, R)$ for a LP sequent
$Γ ⊃ Δ$ is the G3s + $(□\Cut)$ proof $𝒯˚ = (T', R')$ for $Γ˚ ⊃ Δ˚$
inductively defined as follows:

1\. case: The last rule of $𝒯$ is an axiom. Then $𝒯˚$ is just $Γ˚ ⊃ Δ˚$
which is an axiom of G3s.

2\. case: The last rule of $𝒯$ is a $(⊃ →)$ or a $(→ ⊃)$ rule with
premises $S_i$. Then $𝒯˚$ has the same last rule with
$(𝒯↾S_i)˚$ as proofs for the premises $S_i˚$.

3\. case: The last rule of $𝒯$ is a $(⊃ :)_t$ or $(⊃ :)_t$ rule with
premise $S$. Then $𝒯˚$ has a $(⊃ □)$ as last rule with $(𝒯↾S)˚$ as
proof for the premise $S˚$.

4\. case: The last rule of $𝒯$ is a $(⊃ +)$ rule with premise
$S$. Then $𝒯˚$ is $(𝒯↾S)˚$ with the necessary contraction applied.

5\. case: The last rule of $𝒯$ is a $(⊃ ⋅)$ rule with premises $S_0$
and $S_1$. Then $𝒯˚$ has a $(□\Cut)$ as last rule with $(𝒯↾S_i)˚$ as
proofs for the premises $S_i˚$.

6\. case: The last rule of $𝒯$ is a $(⊃ !)$ rule with premise
$S$. Then we get a G3s + $(□\Cut)$ proof for $Γ˚ ⊃ Δ˚, □□A$ from the
proof $(𝒯↾S)˚$ by lemma \ref{boxbox}. $𝒯˚$ is that proof with the
additional $□□A$ removed by contraction as $□□A ∈ Δ˚$.

\End{definition}

To reason about the relations between a G3lp proof $𝒯$ and its
forgetful projection $𝒯˚$, the following algorithm to construct $𝒯˚$
is useful:

1. Replace all sequents by their forgetful projection.

2. Add the additional $(⊃ □)$ rules and prepend additional $□$ where
necessary, so that the forgetful projections of $(⊃ !)$ reduce to
simple contractions.

3. Eliminate all contractions to get a G3s + $(□\Cut)$
proof.

It is not immediately clear that contracting formulas only removes
occurrences as the proof uses inversion which in turn also adds
weakening formulas. But all the deconstructed parts weakened in this
way get contracted again in the next step of the contraction. In the
end the contracted proof tree is always a subset of the original proof
tree. ^[TODO more formal?, subset wrong word]

That means that also $𝒯˚$ is a subset of the tree constructed in step
two. From this we see that all $□$ occurrences in $𝒯˚$ have a term
occurrence in $𝒯$ mapped to them if we consider the extra $□$
occurrences introduced in step 2 of the algorithm (resp. in case
6 of the definition) as replacements of the same term as the $□$
occurrences they are contracted with and also consider the extra
sequents $□Γ ⊃ □A$ introduced in step 2 as copies of the same formulas
in the original sequent $Γ', □Γ ⊃ Δ, □A$ derived by the original
$(⊃ □)$ rule.

\Begin{lemma}
For any family $f_i$ of $□$ symbols in $𝒯˚$ there is a unique proof
term family $\bar{t}_{i'}$ in $𝒯$ such that $s ∈ \bar{t}_{i'}$ for all proof
term occurrences $s$ mapped to $□$ occurrences in $f_i$.
\End{lemma}

\Begin{proof}
For any two directly corresponding $□$ occurrences we show that the
two mapped term occurrences correspond directly or by reflexive closure:

1\.\ case: The two $□$ occurrences are added in step 2 . Then the
mapped term occurrences are the same occurrence and correspond by
reflexive closure.

2\.\ case: The two $□$ occurrence correspond directly by a rule which
is the forgetful projection of a rule in $𝒯$.  Then the mapped term
occurrences also correspond as all G3lp rules with a direct equivalent
in G3s have the same correspondences. Notice that lemma \ref{boxbox}
only removes weakening formulas from existing $(⊃ □)$ rules. So this
still holds for $(⊃ □)$ rules and their corresponding $(⊃ :)$ rules
even after applying lemma \ref{boxbox}.

3\.\ case: The two $□$ occurrences correspond directly by a $(⊃ □)$
rule added in step 2. Then the rule together with the previous rule
has the following form:

\AXC{$□Γ ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$□Γ ⊃ □A$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ', □Γ ⊃ Δ, □□A$}
\DP

As the formulas in $□Γ ⊃ □A$ are considered copies of the original
sequent $Γ', □Γ ⊃ Δ, □A$, and the sequent $Γ', □Γ ⊃ Δ, □□A$ is
considered the same sequent with an $□$ added, the mapped term
occurrences are actually the same and therefore correspond by reflexive
closure.

As direct correspondence in the G3s proof is a subset of
correspondence in the G3lp proof, so is its transitive and reflexive
closure. So for any two corresponding $□$ occurrences of a family
$f_i$ the mapped term occurrences also correspond and therefor belong
to the same family $\bar{t}_{i'}$.
\End{proof}

\Begin{lemma}
If $i ≺ j$ in $𝒯˚$ then either $i' = j'$ or $i' ≺ j'$ in $𝒯$ for the proof term
families $\bar{t}_{i'}$ and $\bar{t}_{j'}$ from the previous lemma.
\End{lemma}

\Begin{proof}

$i ≺ j$ in $𝒯˚$, so there is a $(⊃ □)$ rule in $𝒯˚$ introducing an
occurrence $□_j$ of $f_j$ with an occurrence $□_i$ of $f_i$ in the
premise. For the mapped proof term occurrences $s_i$ and $s_j$ in $𝒯$
we have $s_i ∈ \bar{t}_{i'}$ and $s_j ∈ \bar{t}_{j'}$ by the previous
lemma. From this it follows that $i' ≺ j'$ or $i' = j'$ by an induction on
the proof height:

1\.\ case: The $(⊃ □)$ rule is the forgetful projection of a $(⊃ :)$
rule. Then we have $i' ≺ j'$ directly by the definition of
prehistoric relations for G3lp proofs using the occurrences $s_i$ in
the premise of the rule $(⊃ :)$ introducing the occurrence $s_j$.

3\.\ case: The $(⊃ □)$ rule is added in step 2. Then the rule together
with the previous rule has the following form:

\AXC{$□Γ ⊃ A$}
\RightLabel{$(⊃ □)$}
\UIC{$□Γ ⊃ □_kA$}
\RightLabel{$(⊃ □)$}
\UIC{$Γ', □Γ ⊃ Δ, □_j□_kA$}
\DP

For the term occurrence $s_k$ mapped to the occurrence $□_k$ we have
$s_j = !s_k$ and $s_k ∈ \bar{t}_{j'}$ as $s_j$ is the top level term of the
principal formula of a $(⊃ !)$ rule. If the occurrence $□_i$ is the
occurrence $□_k$ then $i' = j'$ and we are finished. If the occurrence
$□_i$ is not the occurrence $□_k$ then there is a corresponding
occurrence $□'_i$ with a corresponding mapped term $s'_i$ in the
sequent $□Γ ⊃ A$ and we have $i ≺ k$ from the previous $(⊃ □)$. As
$\bar{t}_{j'}$ is also the term family of $s_k$ we get $i' ≺ j'$ or
$i' = j'$ by induction hypothesis on the shorter proof up to the that
$(⊃ □)$ rule with the occurrences $□'_i$, $s'_i$, $□_k$ and $s_k$.
\End{proof}

\Begin{lcorollary}
If $𝒯$ is prehistoric-cycle-free then also $𝒯˚$ is
prehistoric-cycle-free.
\End{lcorollary}

\Begin{proof}
The contraposition follows directly from the lemma as for any cycle
$i_0 ≺ ... ≺ i_n ≺ i_0$ in $𝒯˚$ we get a cycle in $𝒯$ by removing
duplicates in the list $i'_0, ..., i'_n$ of mapped term families
$\bar{t}_{i'_0}, ... \bar{t}_{i'_n}$.
\End{proof}

We will now come back to our example formula $¬□(P ∧ ¬□P)$ from
chapter \ref{self}. Figure \ref{g3lpproof} contains a proof of the
same realization $¬x{:}(P ∧ ¬t⋅x{:}P)$ in G3lp as well as the
forgetful projection of that proof in G3s + (□Cut). For simplicity
we assumed that $(A ∧ B → A)$ is an axiom A0 and therefore $t$ is a
proof constant.

This proofs display the logical dependencies making the formula
self-referential in quite a different way than the original G3s proof
in figure \ref{proofs}. There are 3 families of $□$ in the G3s +
(□Cut) proof. Two are the same families as in the G3s proof, occur
in the root sequent and have a consistent polarity throughout the
proof. We therefore simply use the symbols $⊞$ and $⊟$ for this
families. The third one is part of the cut formula and therefore does
not occur in the final sequent and does not have consistent polarity
throughout the proof. We use $□$ for occurrences of this family in the
proof.

All left prehistoric relations of the proof are from left branch of
the cut where we have $⊟ ≺_L ⊞$ and the cycle $⊞ ≺_L ⊞$. Other than in
the G3s proof, the two $⊞$ are used for different formulas $P$ and $P
∧ ¬□P$ and the connection between the two is established by the
(□Cut) with $□(P ∧ ¬□P → P)$. A similar situation is necessary
for any prehistoric cycle in a G3lp proof as we will show formally.

\afterpage{
\thispagestyle{plain}
\begin{landscape}
\begin{figure} \caption{G3lp proof} \label{g3lpproof}
\vspace{2mm}
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

\vspace{2mm}

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
\UIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞(P ∧ ¬□P), ⊞P$}

\AXC{$P, ¬□P ⊃ P$}
\RightLabel{$(∧ ⊃)$}
\UIC{$P ∧ ¬□P ⊃ P$}
\RightLabel{$(⊃ →)$}
\UIC{$ ⊃ P ∧ ¬□P → P$}
\RightLabel{$(⊃ □)$}
\UIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞(P ∧ ¬□P → P), ⊞P$}

\RightLabel{(□Cut)}
\BIC{$P, ⊟(P ∧ ¬⊞P) ⊃ ⊞P$}
\RightLabel{$(¬ ⊃)$}
\UIC{$P, ¬⊞P, ⊟(P ∧ ¬⊞P) ⊃$}
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


\Begin{lemma}
All occurrences belonging to a proof term family $\bar{t}$ in a
premise $S$ of any $(⊃ :)$ rule are occurrences of the top level term
$t$ itself.
\End{lemma}

\Begin{proof}
All G3lp rules only relate different proof terms if they are top level
proof terms on the right. All occurrences of $s ∈ \bar{t}$ in a
premise $S$ of a $(⊃ :)$ rule correspond either as part of a strict
subformula on the right or as part of a subformula on the left of the
conclusion. A formula on the left can only correspond to a subformula
on the right as a strict subformula. Therefore all corresponding
occurrences of $s$ on the right in the remaining path up to the root
are part of a strict subformula and so all corresponding occurrences
of $s$, left or right, in the remaining path are occurrences of the
same proof term $s$. As $t$ itself is a corresponding occurrences of
$s$ in that path, we get $t = s$.
\End{proof}

\Begin{lcorollary}[TODO] \label{corollary}
If $i ≺ j$ for two term families $\bar{t_i}$ and $\bar{t_j}$ of a G3lp
proof then there is $(⊃ :)$ rule introducing an occurrence $s ∈
\bar{t_j}$ in a formula $s{:}A$ such that there is an occurrence of
$t_i$ in $s{:}A$ (as a term, not as a family, i.e. the occurrence of
$t_i$ is not necessary in $\bar{t_i}$).
\End{lcorollary}

The last corollary gives us a close relationship between prehistoric
relations in G3lp and occurrences of terms in $(⊃ :)$ rules. But it
does not differentate between the two variants $(⊃ :)_c$ and $(⊃ :)_t$
used for introducing elements from $CS$ and input formulas $t:A$ in
the proven sequent itself. It is therefore necessary to expand the
definition of self-referentiality as follows:

\Begin{definition}[Inputs]
The *inputs* $IN$ of a G3lp proof are all LP formulas which are the
principal formula of a $(⊃ :)_t$ or $(⊃ :)_c$ rule.
\End{definition}

Notice that the used constant specifications $CS$ is a subset of the
inputs $IN$. We can now expand the definition of self-referentiality to
input sets in the natural way:

\Begin{definition}[directly self-referential]
The inputs $IN$ of a G3lp proof are *directly self-referential* if there is a
proof term $t$ such that $t{:}A(t) ∈ IN$.
\End{definition}

\Begin{definition}[self-referential]
The inputs $IN$ of a G3lp proof are *self-referential* if there is a
subset $A ⊆ IN$ such that $A := {t_0{:}A(t_1), ..., t_{n-1}{:}A(t_0)}$.
\End{definition}

\Begin{theorem}
If the input set $IN$ of a G3lp proof is non self-referential then the
proof is prehistoric-cycle-free.
\End{theorem}

\Begin{proof}
We show the contraposition. Assume there is a prehistoric cycle $i_0 ≺
i_1 ≺ ... ≺ i_{n-1} ≺ i_0$. By the corollary \ref{corollary} there
exists formulas $s_k{:}A_k$ in $IN$ such that $t_{i_{k}} ∈ \sub(A_k)$
and $s_k ∈ \sub(t_{i_{k'}})$ with $k' := k + 1 \mod n$. From the latter
and $t_{i_{k' }} ∈ \sub(A_{k'})$ follows $s_k ∈ \sub(A_{k' })$. So
$\{s_k{:}A_k\ | 0 ≤ k < n\} ⊆ IN$ is a self-referential subset of $IN$.
\End{proof}

\Begin{corollary}
The forgetful projection $A˚$ of a LP formula provable with a non
self-referential input set $IN$ is provable prehistoric-cycle-free in G3s.
\End{corollary}

Counterexample
--------------

The main result of the last chapter does not exactly match Yu's
result. We have shown that prehistoric cycles in G3s are sufficient for
self-referentiality but only for the expanded definition of
self-referentiality considering the set of all inputs $IN$. The
question arises if this expansion is actually necessary. The following
counterexample shows that indeed, prehistoric cycles in G3s are not
sufficient for needing a self-referential $CS$.

\Begin{lemma}
The S4 formula $A ≡ □(P ∧ ¬□P → P) → ¬□(P ∧ ¬□P)$ has a realization in
$LPG_0$.
\End{lemma}

\Begin{proof}
Set $A^r ≡ y{:}(P ∧ ¬y⋅x{:}P → P) → ¬x{:}(P ∧ ¬y⋅x{:}P)$. We have
$y{:}(P ∧ ¬y⋅x{:}P → P) ⊢_{LPG_0} ¬x{:}(P ∧ ¬y⋅x{:}P)$ by the same
derivation as for $LP ⊢ ¬x{:}(P ∧ ¬t⋅x{:}P)$ replacing the
introduction of $t{:}(P ∧ ¬t⋅x{:}P → P)$ by the assumption $y{:}(P ∧
¬y⋅x{:}P → P)$ and $t$ by $y$. So by the deduction theorem $LPG_0 ⊢
y{:}(P ∧ ¬y⋅x{:}P → P) → ¬x{:}(P ∧ ¬y⋅x{:}P)$.
^[If we assume that $P ∧ ¬y⋅x{:}P → P$ is an axiom A0,
this matches the more general result in corollary 7.2 in @artemov2001
[14]: $LP(CS) ⊢ F$ if and only if $LPG_0 ⊢ CS ⊃ F$.]
\End{proof}

\Begin{lemma}
The S4 formula $□(P ∧ ¬□P → P) → ¬□(P ∧ ¬□P)$ has no prehistoric-cycle-free proof.
\End{lemma}

\Begin{proof}
By inversion for G3s in one direction and an easy deduction in the other, we have
$G3s ⊢ ⊃ □(P ∧ ¬□P → P) → ¬□(P ∧ ¬□P)$ iff $G3s ⊢  □(P ∧ ¬□P → P), □(P ∧
¬□P) ⊃$. In both directions the proofs remain prehistoric-cycle-free if
the other proof was prehistoric-cycle-free. For a proof of $□(P ∧ ¬□P →
P), □(P ∧¬□P) ⊃$ we have two possibilities for the last rule:

1\.\ case: The last rule is a $(□ ⊃)$ rule with $□(P ∧ ¬□P → P)$ as
the principal formula. Then the following proof tree shows that we
need a proof for the sequent $P, □(P ∧ ¬□P → P), □(P ∧¬□P) ⊃$ which is
just the original sequent weakened by $P$ on the left:

\noindent\makebox[\textwidth]{
\AXC{$P ∧¬□P, □(P ∧ ¬□P → P), □(P ∧¬□P) ⊃ P ∧¬□P$}
\RightLabel{$(□ ⊃)$}
\UIC{$□(P ∧ ¬□P → P), □(P ∧¬□P) ⊃ P ∧¬□P$}
\AXC{$P, □(P ∧ ¬□P → P), □(P ∧¬□P) ⊃$}
\RightLabel{$(→⊃)$}
\BIC{$P ∧ ¬□P → P, □(P ∧ ¬□P → P), □(P ∧¬□P) ⊃$}
\RightLabel{$(□ ⊃)$}
\UIC{$□(P ∧ ¬□P → P), □(P ∧¬□P) ⊃$}
\DP
}

So for the remaining of the proof we will have to check if weakening
$P$ on the left helps to construct a prehistoric-cycle-free proof.

2\.\ case: The last rule is a $(□ ⊃)$ rule with $□(P ∧ ¬□P)$ as the
principal formula. We get as premise the sequent $P ∧¬□P, □(P ∧ ¬□P →
P), □(P ∧¬□P) ⊃$ which again by inversion and an easy deduction is
provable prehistoric-cycle-free iff $P, □(P ∧ ¬□P → P), □(P ∧¬□P) ⊃
□P$ is provable prehistoric-cycle-free. It is clear that using $(□ ⊃)$
rules on this sequent just adds additional copies of the existing
formulas.^[TODO more formally?] So by contraction if there is a
prehistoric-cycle-free proof for this sequent, then there is also one
ending in a $(⊃ □)$ rule. The premise of this rule has to have the
form $□(P ∧ ¬□P → P) ⊃ P$ to avoid a prehistoric cycle. But the
following Kripke model shows that $□(P ∧ ¬□P → P) → P$ is not a
theorem of S4 and therefore not provable at all: $w = \{¬P\}, R =
\{(w, w)\}$.  We have $w \Vdash P ∧ ¬□P → P$ because $w \Vdash ¬P$ and
therefore also $w \Vdash ¬(P ∧ ¬□P)$. As $w$ is the only world we get
$w \Vdash □(P ∧ ¬□P → P)$ which leads to the final $w \Vdash ¬(□(P ∧
¬□P → P) → P)$ again because $w \Vdash ¬P$

As all possibilities for a prehistoric-cycle-free proof of $□(P ∧ ¬□P →
P), □(P ∧¬□P) ⊃$ are exhausted, there is no such proof and therefore
also no prehistoric-cycle-free proof of $⊃ □(P ∧ ¬□P → P) → ¬□(P ∧¬□P)$
\End{proof}

\Begin{theorem}
There exists a S4−theorem $A$ and a LP-formula $B$ such that $A$ has
no prehistoric-cycle-free G3s−proof, $B^◦ = A$ and $LP(CS^⊛) ⊢ B$
\End{theorem}

\Begin{proof}
$A := □(P ∧ ¬□P → P) → ¬□(P ∧ ¬□P)$ is a theorem of S4, as $¬□(P ∧ ¬□P)$
already is a theorem of S4. By the previous lemma, there is no
prehistoric-cycle-free proof for $A$ and by the first lemma $B :=
y{:}(P ∧ ¬y⋅x{:}P → P) → ¬x{:}(P ∧ ¬y⋅x{:}P)$ is a realization of $A$
provable in LP0 and therefor also in $LP(CS^⊛)$.
\End{proof}

Conclusion
==========


Literature
==========

