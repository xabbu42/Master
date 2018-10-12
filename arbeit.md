
Introduction
============

Throughout this text, we will only use the modal logik S4 and the logic of proofs LP.

Syntax
======

The language of S4 is given by $A := ⊥ ∣ P ∣ A ∧ A  ∣ A ∨ A ∣ A → A ∣ □A ∣ ◇A$.
By using the known definitions for $∧$, $∨$ and $◇$ by formulas using the remaining syntax, we can reduce that to the minimal language $A := ⊥ ∣ p ∣ A → A ∣ □A$. 

The language of LP consists of terms given by $t := c ∣ x ∣ t ⋅ t ∣ t + t ∣\: !t$ and formulas given by $A := ⊥ ∣ P ∣ A → A ∣ t{:}A$. 

Gentzen Systems for S4 and LP
=============================

In the following text capital greek letters $Γ$, $Δ$ are used for multisets of formulas, latin letters $P$, $Q$ for atomic formulas and latin letters $A$,$B$ for arbitrary formulas. We also use the following shortforms:
$$□Γ := \{□x ∣ x ∈ Γ\}$$
$$Γ,A := Γ ∪ \{A\}$$
$$Γ,Δ := Γ ∪ Δ$$

Throughout this text, we will work with the G3s calculus from []. This is a Gentzen-style calculus with the following rules:

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

Again by using the standard definitions for $∨$, $∧$ and $◇$, we can reduce and simplify the rules to the following minimal but equivalent system:

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

Every symbol occurence in a premise corresponds to at most one symbol occurence in the conclusion. Therefore all symbol occurences in a proof can be divided in disjunct corresponding families of symbol occurences. For us the occurences of the symbol $□$ are of special importance.
 

Main Proof
==========

Yu proofes in [] the following theorem:

Theorem 7 (Necessity of Left Prehistoric Loop for Self-referentiality).
If an S4−theorem $φ$ has a left-prehistoric-loop-free G3s−proof, then there is an LP−formula $ψ$ s.t. $ψ^◦ = φ$ and $⊢_{LP(CS^⊛)} ψ$.

Literature
==========

