
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

Gentzen Systems for S4 and LP
=============================

In the following text capital greek letters $Γ$, $Δ$ are used for
multisets of formulas, latin letters $P$, $Q$ for atomic formulas and
latin letters $A$,$B$ for arbitrary formulas. We also use the
following shortforms:

$$□Γ := \{□x ∣ x ∈ Γ\}$$
$$Γ,A := Γ ∪ \{A\}$$
$$Γ,Δ := Γ ∪ Δ$$

Throughout this text, we will work with the G3s calculus from []. This
is a Gentzen-style calculus with the following rules:

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
\AXC{$Γ, A, □A ⊃ Δ$}
\UIC{$Γ, □A ⊃ Δ$}
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

Similarly we get a Gentzen-Style System for LP with the following rules:

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

\RightLabel{$(⊃ +)_L$}
\AXC{$Γ ⊃ Δ, t{:}A$}
\UIC{$Γ ⊃ Δ, t+s{:}A$}
\DP

&

\RightLabel{$(⊃ +)_R$}
\AXC{$Γ ⊃ Δ, t{:}A$}
\UIC{$Γ ⊃ Δ, s+t{:}A$}
\DP

\\

\RightLabel{$({:} ⊃)$}
\AXC{$A, t{:}A, Γ ⊃ Δ$}
\UIC{$t{:}A, Γ ⊃ Δ$}
\DP

&

\RightLabel{$(⊃ !)$}
\AXC{$Γ ⊃ Δ, t{:}A$}
\UIC{$Γ ⊃ Δ, !t{:}t{:}A$}
\DP

\\

\RightLabel{$(⊃ ⋅)$}
\AXC{$Γ ⊃ Δ, s{:}(A → B)$}
\AXC{$Γ ⊃ Δ, t{:}A$}
\BIC{$Γ ⊃ Δ, s⋅t{:}B$}
\DP

&

\RightLabel{$(⊃ :)$, $A$ an axiom}
\AXC{$Γ ⊃ Δ, A$}
\UIC{$Γ ⊃ Δ, c{:}A$}
\DP

\end{longtable}

In all this rules, arbitrary formulas which occur in the premises and the conclusion (denoted by repeated multisets $Γ$, $Δ$) are called side formulas. Arbitrary formulas which only occur in the conclusion (denoted by new multisets $Γ$, $Δ$, $Γ'$, $Δ'$) are called weakening formulas. The remaining single new formula in the conclusion is called the principal formula of the rule. Notice that weaking formulas only occur in axioms and the rules $(⊃ □)$, $(◇ ⊃)$.

Every symbol occurrence in a premise corresponds to at most one symbol occurrence in the conclusion. Therefore all symbol occurrences in a proof can be divided in disjunct corresponding families of symbol occurrences. For us the occurrences of the symbol $□$ are of special importance.


Annotated S4 Formulas and Proofs
================================

We assign a positive or negative polarity relativ to $A$ to all
subformulas occurrences $B$ in $A$ as follows:

* The only occurrence of $A$ in $A$ has positive polarity.

* If an occurrence $B → C$ in $A$ already has a polarity, then the
  corresponding occurrence of $C$ in $B → C$ has the same polarity and
  the corresponding occurnece of $B$ in $B → C$ has the opposite
  polarity.

* If an occurrence $□B$  already has a polarity, then the corresponding
  occurrence of $B$ in $□B$ has the same polarity.

We want to define an annotated version of S4 formulas by
distinguishing all occurrences of $□$ by subscripts and also marking
if the occurrence has positive or negative polarity.

We therefore define $an_A(B)$ recursively on all occurrences of
subformulas $B$ in $A$ as follows:

* If $B$ is the occurrence of an atomic formula $P$ or $⊥$, then
  $an_A(B) := B$.

* If $B = B_0 → B_1$, then $an_A(B) := an_A(B_0) → an_A(B_1)$

* If $B = □B_0$ and has positive polarity in $A$, then $an_A(B) := ⊞_i
  an_A(B_0)$ for a new $⊞_i$.

* If $B = □B_0$ and has negative polarity in $A$, then $an_A(B) := ⊟_i
  an_A(B_0)$ for a new $⊟_i$.

The annotated version $an(A)$ of $A$ is then $an(A) := an_A(A)$ for
the only occurrence of $A$ in $A$. So for example the annoteded version
of $□((R → □R) → ⊥) → ⊥$ is $⊟_0((R → ⊞_0 R) → ⊥) → ⊥$

For an annotated Gentzen proof of an S4 formula, we first annotate the
root sequent as above, using completely new subscripts for all
formulas. We then use the same annotated box symbol for all
corresponding occurrences of that box in the proof. Every formula $B$
in the proof corresponds to an occurrence of a subformula $B$ in a
formula $A$ of the root sequent. In the annotated proof that formula
$B$ is therefore replaced by $an_A(B)$ of the corresponding occurrence
of $B$ in $A$.

Main Proof
==========

Yu proofes in [] the following theorem:

Theorem 7 (Necessity of Left Prehistoric Loop for
Self-referentiality).  If an S4−theorem $A$ has a
left-prehistoric-loop-free G3s−proof, then there is an LP−formula $B$
s.t. $B^◦ = A$ and $⊢_{LP(CS^⊛)} A$

Literature
==========

