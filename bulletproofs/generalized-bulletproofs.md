# Generalized Bulletproofs

Notation from https://doc-internal.dalek.rs/bulletproofs/notes/r1cs_proof/index.html

## The Relation ("Extended R1CS")

Bulletproofs provide a proof for the following relation:

$$
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} = 
W_V \cdot \vec{v} + \vec{c}
\ \land \ \vec{a_L} \circ \vec{a_R} = \vec{a_O}
$$

Where $\vec{a_L}, \vec{a_R}, \vec{a_O}, \vec{v}$ are the witnesses, with $\vec{v}$ being the opening of a number of (dimension 1) Pedersen commitments. It is not quite the standard def. of R1CS, but clearly equivalent.

Because we are going to have a "pre-committed" vectors $\vec{a_C}$ (a Pedersen commiment of some high dimension), we instead consider a generalization i.e.

$$
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} = W_V \cdot \vec{v} + \vec{c} \\
\ \land \ \\
\vec{a_L} \circ \vec{a_R} = \vec{a_O}
$$

Of course, we could have even more of these committed "linear" terms $\vec{a_C}$, but for simplicity in this explaination let us keep it at 1 -- generalizating it further is an easy exercise left to the reader.

## R1CS $\rightarrow$ Sum of Inner Products

Rewrite:

$$
\vec{a_L} \circ \vec{a_R} - \vec{a_O} = \vec{0}
$$

We can sample $\vec{y} = (1, \ldots, y^{n-1})$ to reduce it to a single field element:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
= 0
$$

The same trick can be applied to every row of $W_L, W_R, W_V, W_C, W_O$ by sampling $\vec{z} = (1, \ldots, z^{n-1})$ and noting:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle
= 0
\land
W_L \cdot \vec{a_L} + 
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} -
W_V \cdot \vec{v} - 
\vec{c}
= \vec{0}
$$

If and only if (with overwhelming probability over $z$):

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle +
z \cdot
\langle 
\vec{z},
W_L \cdot \vec{a_L} +
W_R \cdot \vec{a_R} +
W_O \cdot \vec{a_O} +
W_C \cdot \vec{a_C} -
W_v \cdot \vec{v} -
\vec{c}
\rangle
= 0
$$

(we went from an equation over vectors to single field elements using a challenge $z$)
    
Moving stuff around and separating the inner products, rewrite the second part of the expression:

$$
\langle z \vec{z} \cdot W_L, \vec{a_L} \rangle + 
\langle z \vec{z} \cdot W_R, \vec{a_R} \rangle +
\langle z \vec{z} \cdot W_O, \vec{a_O} \rangle +
\langle z \vec{z} \cdot W_C, \vec{a_C} \rangle -
\langle z \vec{z} \cdot W_V, \vec{v} \rangle -
\langle z \vec{z}, \vec{c} \rangle
= 0
$$

Let us define:

$$
\vec{w_L} = z \cdot \vec{z} \cdot W_L \in \mathbb{F}^n, \
\vec{w_R} = z \cdot \vec{z} \cdot W_R \in \mathbb{F}^n, \
\vec{w_V} = z \cdot \vec{z} \cdot W_V \in \mathbb{F}^n, \
\vec{w_C} = z \cdot \vec{z} \cdot W_C \in \mathbb{F}^n, \
\vec{w_O} = z \cdot \vec{z} \cdot W_O \in \mathbb{F}^n,  \
w_c = \langle z \cdot \vec{z}, \vec{c} \rangle \in \mathbb{F} 
$$

Note that the verifier can just compute these vectors by himself (since the matrixes, the circuit relation, is public). We are now left with:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R} - \vec{a_O}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\langle
\vec{y},
\vec{a_O}
\rangle+
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Which enforces sat. of the extended R1CS.

However, the expression above has *many* inner products. Since we need to do a folding argument for every inner product we would like to avoid this, so, how do we reduce these to a single inner product? First an intermezzo.

## Intermezzo: Vector Polynomials

### Definition

An "$n$" dimensional "vector polynomial" consists of $n$ polynomials "in parallel":
$$
\vec{f}(X) = (f_1(X), \ldots, f_n(X)) = \sum_{i=0}^d \vec{a_i} \cdot  X^i \in \mathbb{F}[X]^n
$$

A polynomial over the $\mathbb{F}$-module $\mathbb{F}^n$. Note that for $x \in \mathbb{F}$ we get $\vec{f}(x) \in \mathbb{F}^n$

This notion is useful, because Pedersen commitments allow us to commit to a vector polynomial efficiently (independently of the dimension) and homomorphically evaluate every coordinate of the vector polynomial:

$$
\mathsf{Com}(\vec{f}(X)) = (\mathsf{PedersenVec}(\vec{a_0}), \ldots, \mathsf{PedersenVec}(\vec{a_d}))
$$

($d$ commitments to $n$-dimensional vectors)

### Inner Product of Vector Polyomials

The "inner product" between two vector polynomials is defined in the intuitive way (for any module over any ring):  taking the coordinate-wise product of polynomials and summing:
$$
\langle
\vec{f}(X), \vec{g}(X)
\rangle = \sum_i f_i(X) \cdot g_i(X) 
\in \mathbb{F}[X]
$$

Note that $\forall x. \langle
\vec{f}, \vec{g}
\rangle(x) = \langle \vec{f}(x), \vec{g}(x)\rangle$ and $\deg(\langle \vec{f}, \vec{g} \rangle) = \deg(\vec{f}) + \deg(\vec{g})$.

This already hints at the approach to check correctness of an inner product between vector polynomials, since we can homomorphically compute commitments to $\vec{f}(x) \in \mathbb{F}$ and $\vec{g}(x) \in \mathbb{F}$ at any public $x$ efficiently by operating on the commitments to the coefficients, to check $\langle \vec{f}, \vec{g} \rangle = \vec{h}$ at a random point $x$

## Sum of Inner Products $\rightarrow$ Single Inner Product

Let us now see why inner products between vector polynomials are useful to us. 

Suppose we have two inner products:

$$
\Delta = \langle \vec{a}, \vec{b} \rangle + \langle \vec{c}, \vec{d} \rangle
$$

If I define the vector polynomials (left/right):

$$
\vec{f_L}(X) = \vec{a} \cdot X + \vec{c} \cdot X^2
$$

$$
\vec{f_R}(X) = \vec{b} \cdot X + \vec{d}
$$

And consider the inner product, then $\Delta$ lands in the square term:

$$
\langle \vec{f_L}, \vec{f_R} \rangle(X) = \delta_0 + \delta_1 \cdot X + \Delta \cdot X^2 + \delta_3 \cdot X^3
\in \mathbb{F}[X]$$

Where $\delta_0, \delta_1, \delta_3$ are some cross-term garbage.

More generally: we define a "left polynomial" where powers *increase* for every left term in the series of inner products and a "right polynomial" where the powers *decrease* for every right term, then the terms will "align" at the "middle power". i.e. in general, suppose we have:

$$
\Delta = \sum_{i=1}^t \langle \vec{L_i}, \vec{R_i} \rangle
$$

Then we define:

$$
\vec{f_L}(X) = \sum_{i=1}^t \vec{L_i} \cdot X^i
$$
$$
\vec{f_R}(X) = \sum_{i=1}^{t} \vec{R_i} \cdot X^{t - i} 
$$

In which case, the $t$'th coeficient of $\langle \vec{f_L}, \vec{f_R} \rangle(X)$ is $\Delta$, neato!

This observation suggest the following approach to reduce a sum of multiple inner products, given commitments to every vector, to a single inner product as follows:

1. Prover sends commitments to $\{ \delta_i \}_{i \in 0, \ldots, 2 \cdot t - 1}$ the coefficients, were we are intrested in $\delta_t = \Delta$, which is usually implicit (e.g. fixed to $0$). Then both parties locally define:
$$
\vec{f_L}(X) = \sum_{i=1}^t \vec{L_i} \cdot X^i \in \mathbb{F}[X]^n
$$
$$
\vec{f_R}(X) = \sum_{i=1}^{t} \vec{R_i} \cdot X^{t - i} \in \mathbb{F}[X]^n
$$
$$
g(X) = \sum_{i = 0}^{2 \cdot t - 1} \delta_i \cdot X^i \in \mathbb{F}[X]
$$
2. Verifier samples $x \gets \mathbb{F}$
3. Both sides compute commitments to the vectors:
$$
\vec{f_L}(x), \vec{f_R}(x)\in \mathbb{F}^n
$$

And a commitment to the field element $g(x) \in \mathbb{F}$, using the homomorphic property of the Pedersen commitments. We now have just a single inner product claim about Pedersen commitments:

$$
\langle \vec{f_L}(x), \vec{f_R}(x) \rangle = g(x)
$$

## Hadamard Products between Secrets and Public Values

Given $\mathsf{PedersenVec}_{\vec{G}}(\vec{V})$ we can simply define 
$$
\mathsf{PedersenVec}_{[\vec{C}^{-1}] \ \circ \ \vec{G}}(\vec{V} \circ \vec{C}) =
\mathsf{PedersenVec}_{\vec{G}}(\vec{V})
$$
In other words, we can homomorphically compute a Hadamard product, where one side is public, simply by a change of basis: rather than a commitment to $\vec{V}$ in basis $\vec{G}$ it is a commitment to $\vec{V} \circ \vec{C}$ in basis $\left[\vec{C}^{-1}\right] \circ \vec{G}$, in other words: if the commitment was opened you would check the correctness by re-commiting using $\left[\vec{C}^{-1}\right] \circ \vec{G}$.

## What Inner Products?

Now that we have the components let us massage our expression from before:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\langle
\vec{y},
\vec{a_O}
\rangle+
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

We are going to massage this so that it is on a form where our newly dicussed techniques apply, we have two goals:

1. Reduce the number of inner products (for efficiency) by collecting common terms.
2. Get rid of the Hadamard product betwen two secrets: $\vec{a_L} \circ \vec{a_R}$.

Start by combining $\vec{a_O}$ terms:

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle -
\textcolor{brown}{\langle \vec{y}, \vec{a_O} \rangle} +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\textcolor{brown}{\langle \vec{w_O}, \vec{a_O} \rangle} +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\textcolor{brown}{\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle} +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Note that the left size of the inner product $\langle \vec{y}, \vec{a_L} \circ \vec{a_R} \rangle$ is public, so lets move one secret to each side, using $\langle \vec{y}, \vec{a_L} \circ \vec{a_R} \rangle = \langle \vec{a_L}, \vec{y} \circ \vec{a_R} \rangle$ get rid of the Hadamard product between secret values:

$$
\textcolor{magenta}{
\langle
\vec{y},
\vec{a_L} \circ \vec{a_R}
\rangle} +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\textcolor{magenta}{ \langle \vec{a_L}, \vec{y} \circ \vec{a_R} \rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\langle \vec{w_R}, \vec{a_R} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Note that we *know* how to deal with a Hadamard product between a secret and a public value.

Using $\textcolor{blue}{\langle \vec{a_R}, \vec{w_R} \rangle = \langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle}$ rewrite:

$$
\langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\textcolor{blue}{\langle \vec{w_R}, \vec{a_R} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


<center><b>Becomes</b></center>

$$
\langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle + 
\textcolor{blue}{\langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Collect $\vec{y} \circ \vec{a_R}$ terms (our motivation for the previous step):

$$
\textcolor{green}{ \langle
\vec{a_L}, \vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle + 
 \textcolor{green}{ \langle  \vec{w_R} \circ (\vec{y})^{-1}, \vec{a_R} \circ \vec{y} \rangle} +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle = \\
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$


<center><b>Becomes</b></center>

$$
\textcolor{green}{ \langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1},\vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle = \\
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

Add $\textcolor{red}{\delta(y, z) = \langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle}$ to both sides:

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_L}, \vec{a_L} \rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle +
\langle \vec{w_C}, \vec{a_C} \rangle +
\textcolor{red}{\langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle} \\ = 
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\textcolor{red}{\delta(y, z)}
\in \mathbb{F}
$$

Note that $\delta(y, z)$ does not depend on the witness! (the verifier can compute it)

Combine $\vec{w_L}$ terms:

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\textcolor{orange}{\langle \vec{w_L}, \vec{a_L} \rangle} + 
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\textcolor{orange}{\langle (\vec{y})^{-1} \circ \vec{w_R}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\textcolor{orange}{\langle (\vec{y})^{-1} \circ \vec{w_R} + \vec{a_L}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

Combine $\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}$ terms:

$$
\textcolor{purple}{
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R}
\rangle } +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle \\ + 
\langle \vec{w_C}, \vec{a_C} \rangle +
\textcolor{purple}{\langle (\vec{y})^{-1} \circ \vec{w_R} + \vec{a_L}, \vec{w_L} \rangle} =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

<center><b>Becomes</b></center>

$$
\textcolor{purple}{
\langle
\vec{a_L} + \vec{w_R} \circ (\vec{y})^{-1}, \vec{y} \circ \vec{a_R} +\vec{w_L}
\rangle } +
\langle \vec{w_O} - \vec{y}, \vec{a_O} \rangle + 
\langle \vec{w_C}, \vec{a_C} \rangle \\ =
\langle \vec{w_V}, \vec{v} \rangle +
w_c +
\delta(y, z)
\in \mathbb{F}
$$

So in the end we have 3 inner products on the left: in general we would be left with $2 + m$ inner products of $m$ vector Pedersen commitments. All these are combined into a single inner product using the previous technique based on vector polynomials.

Note that during verification the right side is a commitment to a single field element!

## The Folding Argument: Just Regular Bulletproofs from Here.

At this point we have a single inner product to verify.

The folding argument (not covered here) proves:

$$
\left\{
    (
    \vec{a} \in \mathbb{F}^{n},
    \vec{b} \in \mathbb{F}^{n}
    )
    : P = \langle \vec{a}, \vec{G} \rangle + \langle \vec{b}, \vec{H} \rangle \land c = \langle \vec{a}, \vec{b} \rangle
\right\}
$$

---

# Protocol Spec

The sections above derive *what* the prover and verifier are checking. The sections below describe *how* the protocol is actually run end-to-end in this crate, including:

- the polynomial layout (which secret goes into which coefficient of `l(X)` / `r(X)`);
- the synthetic target coefficient `t_D`;
- the vector-commitment specialization used here (no $c_{k,R}$ term, same as monero);
- the `T` polynomial transmission and the `tau_x` blinding accumulator;
- the `mu` blinding accumulator (`e_blinding` in the code);
- the full 5-move protocol and how it is compressed using the inner-product argument;
- the two-phase extension (`A_I2 / A_O2 / S2` weighted by `u`);
- the verifier's MSM equation;
- the Fiat-Shamir transcript order.

The notation `D = op_degree = 2c + 2` is used throughout, where `c = ncomm` is the number of vector commitments. `mid = D/2 = c + 1`.

## Polynomial layout

The prover builds two vector polynomials $l(X), r(X) \in \mathbb{F}[X]^n$ of degree $D + 1$. Each coefficient is itself a length-$n$ vector. The slots are assigned as:

| slot $d$ | $l(X)[d]$ | $r(X)[d]$ |
| --- | --- | --- |
| $0$ | $0$ | $w_O - y^n$ |
| $1$ | $0$ | $w_{C_1}$ |
| $2$ | $0$ | $w_{C_2}$ |
| $...$ | $...$ | $...$ |
| $c$ | $0$ | $w_{C_c}$ |
| $mid = c + 1$ | $a_L + y^{-1} \circ w_R$ | $y^n \circ a_R + w_L$ |
| $c + 2 = D - c$ | $a_{C_c}$ | $0$ |
| $...$ | $...$ | $...$ |
| $D - 1$ | $a_{C_1}$ | $0$ |
| $D$ | $a_O$ | $0$ |
| $D + 1$ | $s_L$ | $y^n \circ s_R$ |

where $a_{C_k}$ is the $k$-th vector commitment's value vector (1-indexed: $k=1$ is the first one created) and $w_{C_k}$ is the public weight vector for that commitment. The value vector $a_{C_k}$ sits in the *high* left slot $l[D-k]$ and its public weight $w_{C_k}$ in the *low* right slot $r[k]$; the two degrees sum to $D$, so the product $\langle a_{C_k}, w_{C_k} \rangle$ lands in $t_D$. (This is what keeps all of $l(X)$'s support at or above $mid$ — see invariant 1 below.)

The pair $(D - k, k)$ for $k \in \{1, ..., c\}$ is the slot for the $k$-th vector commitment. The midpoint $(mid, mid)$ is the slot for $a_L / a_R$. The pair $(D, 0)$ is the slot for $a_O$. The pair $(D+1, D+1)$ is the slot for the masking vectors $s_L, s_R$.

A few invariants follow from this layout:

1. $l(X)$ has no support on coefficients $0..mid-1$. So $l(X) = X^{mid} \cdot l'(X)$ for some $l'(X)$.
2. $t(X) = \langle l(X), r(X) \rangle$ therefore has no support on coefficients $0..mid-1$.
3. The "target" coefficient where all desired inner products collide is $t_D$.
4. Coefficients $t_d$ for $d \in \{mid, ..., D-1, D+1, ..., 2D+2\}$ are committed by the prover via $T_d$ points.
5. Coefficient $t_D$ is *not* committed; it is reconstructed by the verifier from public data and the committed $V$ and $C_k$ points.

TODO: Explain why $D = 2c + 2$ is forced (it is the smallest even $D$ such that the complementary pairs $\{(D-k, k) : k = 1..c\}$ are all distinct from $(mid, mid)$ and $(D, 0)$).

## The synthetic target coefficient $t_D$

By the manipulation in the section "What Inner Products?", $t_D$ equals

$$
t_D = \langle a_L + \vec{y}^{-1} \circ \vec{w_R}, \ \vec{y} \circ a_R + \vec{w_L} \rangle + \langle a_O, \vec{w_O} - \vec{y} \rangle + \sum_{k=1}^c \langle a_{C_k}, \vec{w_{C_k}} \rangle.
$$

When the constraints are satisfied (i.e. the relation holds), this rearranges to

$$
t_D = \langle \vec{w_V}, \vec{v} \rangle + w_c + \delta(y, z),
$$

where $\delta(y, z) = \langle \vec{y}^{-1} \circ \vec{w_R}, \vec{w_L} \rangle$. The RHS is verifier-computable up to $\vec{v}$, which the verifier sees only as commitments $V_i$. So the verifier reconstructs

$$
t_D \cdot B = (\sum_i w_{V,i} v_i) \cdot B + (w_c + \delta(y, z)) \cdot B
$$

via the commitments $V_i = v_i \cdot B + v_{\text{blinding},i} \cdot B_{\text{blinding}}$ (scaled by $w_{V,i}$) plus a $B$ term for $w_c + \delta(y, z)$.

The verifier does *not* see $t_D$ directly; it sees $t_x = t(x)$ and reconstructs $t_x = \sum_{d \neq D} t_d \cdot x^d + t_D \cdot x^D$, where the $t_d$ terms come from $T_d$ commitments and $t_D$ comes from this synthetic reconstruction. See the verifier MSM section below for the full equation.

## Vector commitment specialization

The fixed Generalized Bulletproofs draft defines each vector commitment as

$$
C_k = c_{k,L}^T G + c_{k,R}^T H + c'_k \cdot H'
$$

with $c_{k,L}$ the value vector, $c_{k,R}$ a per-coordinate blinding vector, and $c'_k$ a common scalar mask. The draft populates both the high-left slot $l[D-k] = c_{k,L}$ and the high-right slot $r[D-k] = y^n \circ c_{k,R}$.

This crate uses the simpler form (same as `monero-oxide`):

$$
C_k = c_{k,L}^T G + c'_k \cdot B_{\text{blinding}}
$$

with no $c_{k,R}$ term. So the high-right slot $r(X)[D-k]$ is left as zero. The committed witness is just $(c'_k, c_{k,L})$ -- the tuple `(vec_open[j].0, vec_open[j].1)` in the code.

This change is consistent with monero's audit; soundness is preserved because $c_{k,R}$ does not appear in any constraint relation. Hiding is preserved because the masking vector $s_L$ (at slot $D+1$) provides per-coordinate hiding for $l(X)$ at evaluation time $x$.

## $T$ polynomial commitments

Let $t\_poly\_deg = 2 (D + 1)$ be the degree of $t(X)$. The prover commits to $t_d$ for $d \in T_{\text{xmit}}$, where

```
T_xmit = { mid, mid+1, ..., D-1, D+1, ..., t_poly_deg }
```

(skipping $d = D$ because $t_D$ is the synthetic coefficient; skipping $d < mid$ because those $t_d$ are guaranteed zero by the layout). The total transmitted count is $t\_poly\_deg + 1 - mid - 1 = t\_poly\_deg - mid$.

For each $d \in T_{\text{xmit}}$, the prover samples a random blinding $b_d$, computes

$$
T_d = t_d \cdot B + b_d \cdot B_{\text{blinding}},
$$

and appends $T_d$ to the transcript with label `b"t_poly"` (preceded by the degree as a `u64` with label `b"t_poly degree"`).

## $\tau_x$ (the t-poly blinding evaluation)

The prover defines a blinding polynomial $t\_blinding(X)$ of degree $t\_poly\_deg$:

- $t\_blinding(X)[d] = b_d$ for $d \in T_{\text{xmit}}$ (random, set above);
- $t\_blinding(X)[D] = \sum_i w_{V,i} \cdot v_{\text{blinding},i}$ (synthetic, matches what the verifier reconstructs at $d = D$);
- $t\_blinding(X)[d] = 0$ for all other $d$ (the $0..mid-1$ low coefficients are all zero).

Then $\tau_x = t\_blinding(x)$. This is sent in the proof.

The verifier reconstructs $\tau_x$ from $T_d$ and $V_i$ commitments. See the verifier MSM section below for the exact balance.

## $\mu$ (the `e_blinding` accumulator)

The prover defines $\mu$ (called `e_blinding` in the code) as the weighted sum of *all* commitment blindings, where each blinding is weighted by the power of $x$ at which the corresponding secret vector lands in $l(X)$:

$$
\mu = i_{\text{blinding}} \cdot x^{mid} + o_{\text{blinding}} \cdot x^{D} + s_{\text{blinding}} \cdot x^{D+1} + \sum_{k=1}^{c} \gamma_k \cdot x^{D-k},
$$

where $i_{\text{blinding}} = i_{\text{blinding1}} + u \cdot i_{\text{blinding2}}$ and similarly for $o_{\text{blinding}}$, $s_{\text{blinding}}$ (two-phase extension; see below). The $\gamma_k = \text{vec_open}[j].0$ are the vector-commitment masks.

These weights are exactly the scalars the verifier applies to $A_I, A_O, S, C_k$ when reconstructing $P$ (next section). Since each commitment carries its blinding times $B_{\text{blinding}}$, the aggregate $B_{\text{blinding}}$ component of the reconstructed $P$ is precisely $\mu \cdot B_{\text{blinding}}$ -- matching the $\mu \cdot B_{\text{blinding}}$ term in $P = \ell^T G + r^T H' + \mu \cdot B_{\text{blinding}}$, so in the batched MSM the two appear as $+\mu$ and $-\mu$ and cancel (see "Why the $B_{\text{blinding}}$ coefficient balances").

## The 5-move protocol (uncompressed)

This is the protocol per the fixed draft, in the form before applying the inner-product argument. The compressed form (next section) replaces moves 5/6 with an IPP.

### Move 1 (prover): commit to witness and masking

Prover samples $i_{\text{blinding}}, o_{\text{blinding}}, s_{\text{blinding}} \in \mathbb{F}$ and $s_L, s_R \in \mathbb{F}^n$ (all random). Computes:

$$
A_I = \langle a_L, G \rangle + \langle a_R, H \rangle + i_{\text{blinding}} \cdot B_{\text{blinding}}
$$
$$
A_O = \langle a_O, G \rangle + o_{\text{blinding}} \cdot B_{\text{blinding}}
$$
$$
S   = \langle s_L, G \rangle + \langle s_R, H \rangle + s_{\text{blinding}} \cdot B_{\text{blinding}}
$$

For each vector commitment $k$, the witness $(\gamma_k, c_{k,L})$ is committed as:

$$
C_k = \langle c_{k,L}, G \rangle + \gamma_k \cdot B_{\text{blinding}}
$$

Prover sends $(C_1, ..., C_c, A_I, A_O, S)$ to verifier.

### Move 2 (verifier): sample $y, z$

Verifier samples $y, z \in \mathbb{F}^*$ via Fiat-Shamir. Both sides compute:

- power vectors $\vec{y} = (1, y, ..., y^{n-1})$, $\vec{y}^{-1}$, $\vec{z} = (z, z^2, ..., z^Q)$ where $Q$ is the number of constraints;
- the flattened weights $\vec{w_L}, \vec{w_R}, \vec{w_O}, \vec{w_V}, \vec{w_{C_k}}$ and the constant $w_c$;
- the correction $\delta(y, z) = \langle \vec{y}^{-1} \circ \vec{w_R}, \vec{w_L} \rangle$.

### Move 3 (prover): commit to $t(X)$ coefficients

Prover constructs $l(X), r(X)$ per the polynomial layout above, computes $t(X) = \langle l(X), r(X) \rangle$, samples random $b_d$ for each $d \in T_{\text{xmit}}$, and commits $T_d = t_d \cdot B + b_d \cdot B_{\text{blinding}}$ for each $d \in T_{\text{xmit}}$. Sends all $T_d$ to the verifier.

### Move 4 (verifier): sample $x$

Verifier samples $x \in \mathbb{F}^*$ via Fiat-Shamir.

### Move 5 (prover): evaluate and send

Prover computes:

$$
\ell  = l(x)  \in \mathbb{F}^n,\qquad
r     = r(x)  \in \mathbb{F}^n,\qquad
\hat{t} = \langle\ell, r\rangle  = t(x),
$$
$$
\tau_x = t_{\text{blinding}}(x),\qquad
\mu   = (\text{the weighted-blinding accumulator described above}).
$$

Sends $(\hat{t}, \tau_x, \mu, \ell, r)$. (In the compressed form below, $\ell, r$ are not sent directly; instead an IPP proves the inner product.)

### Verifier's checks

Verifier checks two equations:

1. The $t$-equation:

    $$
    \hat{t} \cdot B + \tau_x \cdot B_{\text{blinding}} \overset{?}{=} \left( w_c + \delta(y, z) \right) \cdot x^D \cdot B + \sum_i w_{V,i} \cdot x^D \cdot V_i + \sum_{d \in T_{\text{xmit}}} x^d \cdot T_d.
    $$

2. The $P$-equation:

    $$
    P \overset{?}{=} \langle \ell, G \rangle + \langle r, H' \rangle + \mu \cdot B_{\text{blinding}}
    $$

    where $H'_i = y^{-i} \cdot H_i$ and $P$ is the verifier's reconstruction from commitments:

    $$
    P = x^{mid} \cdot A_I + x^D \cdot A_O + x^{D+1} \cdot S + \sum_{k=1}^{c} x^{D-k} \cdot C_k + (\text{Hadamard-with-public correction terms}).
    $$

The Hadamard-with-public correction is from the $\vec{y} \circ a_R$ and $\vec{y}^{-1} \circ \vec{w_R}$ rewrites; see the verifier MSM section for the explicit form.

## Compressing via the inner-product argument

In move 5, instead of sending $\ell, r$ explicitly, the prover invokes the Bulletproofs inner-product argument on the relation

$$
P + \hat t \cdot Q = \langle \ell, G \rangle + \langle r, H' \rangle + \hat t \cdot Q \quad \text{with claim} \quad \hat t = \langle \ell, r \rangle,
$$

where $Q = w \cdot B$ for a fresh Fiat-Shamir challenge $w$ (sampled after $\hat{t}, \tau_x, \mu$ are appended). The IPP produces $\log_2(n)$ $(L_j, R_j)$ pairs plus two folded scalars $(a, b)$.

The verifier then runs `verification_scalars` to recover the IPP coefficients $s_i$ (and the inverse squared challenges) and combines them with the rest of the verifier equation in a single MSM. See the verifier MSM section.

## The two-phase extension

This supports a *two-phase* constraint system: phase 1 commits to multipliers known up front; phase 2 commits to extra multipliers allocated inside a randomized callback (after seeing a Fiat-Shamir challenge over the phase-1 commitments).

### Witness split

The witness vectors are split:

- $a_L = a_L^{(1)} \| a_L^{(2)}$, $a_R = a_R^{(1)} \| a_R^{(2)}$, $a_O = a_O^{(1)} \| a_O^{(2)}$, $s_L = s_L^{(1)} \| s_L^{(2)}$, $s_R = s_R^{(1)} \| s_R^{(2)}$
- $n = n_1 + n_2$, where $n_1$ is the phase-1 size (set after `commit_vec` padding) and $n_2$ is the phase-2 size (set after the randomized callback runs).

### Commitments

The prover commits each piece separately:

$$
\begin{aligned}
A_{I1} &= \langle a_L^{(1)}, G_{[0..n_1]} \rangle + \langle a_R^{(1)}, H_{[0..n_1]} \rangle + i_{\text{blinding1}} \cdot B_{\text{blinding}} \\
A_{O1} &= \langle a_O^{(1)}, G_{[0..n_1]} \rangle + o_{\text{blinding1}} \cdot B_{\text{blinding}} \\
S_1    &= \langle s_L^{(1)}, G_{[0..n_1]} \rangle + \langle s_R^{(1)}, H_{[0..n_1]} \rangle + s_{\text{blinding1}} \cdot B_{\text{blinding}} \\[6pt]
A_{I2} &= \langle a_L^{(2)}, G_{[n_1..n]} \rangle + \langle a_R^{(2)}, H_{[n_1..n]} \rangle + i_{\text{blinding2}} \cdot B_{\text{blinding}} \\
A_{O2} &= \langle a_O^{(2)}, G_{[n_1..n]} \rangle + o_{\text{blinding2}} \cdot B_{\text{blinding}} \\
S_2    &= \langle s_L^{(2)}, G_{[n_1..n]} \rangle + \langle s_R^{(2)}, H_{[n_1..n]} \rangle + s_{\text{blinding2}} \cdot B_{\text{blinding}}
\end{aligned}
$$

$A_{I1}, A_{O1}, S_1$ are appended to the transcript *before* the randomized callbacks run (so the challenges sampled inside the callbacks depend on them). $A_{I2}, A_{O2}, S_2$ are appended after. If $n_2 = 0$, the phase-2 commitments are identity.

### $u$ challenge

After all six commitments are in the transcript, a fresh challenge $u$ is sampled (with label `b"u"`). This $u$ is used to:

1. Weight the phase-2 commitments in the verifier's reconstruction: $A_{I2}$ gets scalar $x^{mid} \cdot u$, $A_{O2}$ gets $x^D \cdot u$, $S_2$ gets $x^{D+1} \cdot u$.
2. Scale the phase-2 entries of the IPP basis. Concretely, the prover passes $G_{\text{factors}} = [1; n_1] \| [u; n_2 + \text{pad}]$ and $H_{\text{factors}} = y^{-i} \cdot G_{\text{factors}}[i]$ to the IPP, which operates on the scaled basis $G_i \cdot G_{\text{factors}}[i]$, $H_i \cdot H_{\text{factors}}[i]$.

### Combined blinding accumulator

The single blinding $i_{\text{blinding}}$ in $\mu$ becomes

$$
i_{\text{blinding}} = i_{\text{blinding1}} + u \cdot i_{\text{blinding2}}
$$

and similarly for $o_{\text{blinding}}, s_{\text{blinding}}$. This matches the verifier's scalar pattern: $A_{I1}$ gets $x^{mid}$, $A_{I2}$ gets $x^{mid} \cdot u$, so the $B_{\text{blinding}}$ contributions sum to $(i_{\text{blinding1}} + u \cdot i_{\text{blinding2}}) \cdot x^{mid} = i_{\text{blinding}} \cdot x^{mid}$, which is exactly the term in $\mu$.

### Padding invariant

The phase-2 extension is only safe in combination with vector commitments when $\dim(c_{k,L}) \le n_1$ for every $k$. This is enforced by the prover's padding loop:

```rust
while self.size() > self.secrets.a_L.len() as u32 {
    self.allocate_multiplier(Some((zero, zero)))?;
}
let n_1 = self.size();
```

After this loop, $n_1 \ge \max_k \dim(c_{k,L})$, so every vector commitment's value vector lives entirely in phase-1 coordinates. The verifier mirrors the same padding.

### Vector commitments do not split

Vector commitments are always phase-1 objects. `commit_vec` is not exposed on `RandomizingProver` / `RandomizingVerifier`, so no new vector commitment can be created in the randomized phase.

## The full verifier MSM

The verifier batches both the $t$-equation and the $P$-equation into a single MSM. Let $r$ be a fresh random scalar (sampled per verifier run, used to give the $t$-equation independent weight). Let $w$ be the Fiat-Shamir challenge for $Q = w \cdot B$. Let $(a, b)$ be the IPP folded scalars and $(u_{\text{sq},j}, u_{\text{inv\_sq},j}, s_i)$ be the IPP verification scalars.

The verifier asserts that the following MSM equals the identity:

$$
\sum_{k=1}^{c}  C_k       \cdot x^{D-k} \\
{+} A_I1   \cdot x^{mid}                + A_I2   \cdot x^{mid} \cdot u
{+} A_O1   \cdot x^{D}                  + A_O2   \cdot x^{D} \cdot u
{+} S1     \cdot x^{D+1}                + S2     \cdot x^{D+1} \cdot u
{+} \sum_i V_i  \cdot w_{V,i} \cdot r \cdot x^{D}
{+} \sum_{d \in T_{xmit}} T_d \cdot r \cdot x^{d}
{+} \sum_{j=1}^{\log n} L_j \cdot u_{sq,j} + \sum_{j=1}^{\log n} R_j \cdot u_{inv\_sq,j}
{+} B           \cdot \left( w (\hat{t} - a b) + r ( x^D (w_c + \delta) - \hat{t} ) \right)
{+} B_{blinding} \cdot \left( -\mu - r \cdot \tau_x \right)
{+} \sum_i G_i  \cdot u_{g,i} \cdot \left( x^{mid} \cdot y^{-i} \cdot w_{R,i} - a \cdot s_i \right)
{+} \sum_i H_i  \cdot u_{h,i} \cdot \left( y^{-i} \cdot (\text{comb}_i - b \cdot s_{rev,i}) - 1 \right)
\overset{?}{=}\ \mathcal{O}
$$

where:

- $u_{g,i}$ / $u_{h,i}$ are the phase-2 separator scaling $G_i$ / $H_i$ respectively: $u_{g,i} = u_{h,i} = 1$ for $i < n_1$, else $u$;
- $s_{\text{rev},i} = s[n-1-i]$ (IPP $s$ reversed);
- $\text{comb}_i = x^{mid} \cdot w_{L,i} + 1 \cdot w_{O,i} + \sum_{k=1}^c x^k \cdot w_{C_k,i}$ (the right-poly public combination at coordinate $i$).

When the proof is valid, both the $B$ and $B_{\text{blinding}}$ coefficients evaluate to zero (the $r$-weighted $t$-equation and the unweighted $\mu$-cancellation respectively), and each $G_i, H_i$ coefficient evaluates to zero (the IPP relation $\ell_i = a \cdot s_i$ and $r_i = b \cdot s_{\text{rev},i}$ in the scaled basis).

### Why the $B$ coefficient balances

Expand the $B$ term:

$$
w(\hat t - ab) + r \left( x^D (w_c + \delta) - \hat t \right) + r \cdot x^D \cdot \sum_i w_{V,i} \cdot v_i + r \cdot \sum_{d \in T_{xmit}} x^d \cdot t_d
$$

The IPP relation gives $ab = \hat{t}$, so $w(\hat{t} - ab) = 0$.

Substituting $\hat{t} = t(x) = \sum_{d=0}^{2D+2} t_d \cdot x^d$ and noting $t_d = 0$ for $d < mid$ and $t_D = w_c + \delta + \langle w_V, v \rangle$ (the synthetic relation), the $r$-weighted part reduces to

$$
r \cdot \left( x^D \cdot (w_c + \delta + \langle w_V, v \rangle) + \sum_{d \in T_{xmit}} x^d \cdot t_d - t(x) \right) = r \cdot \left( \sum_{d \neq D, d \ge mid} t_d x^d + x^D \cdot t_D - t(x) \right) = 0.
$$

### Why the `B_blinding` coefficient balances

Expand the $B_{\text{blinding}}$ term and collect all blinding contributions from the commitments:

$$
-\mu - r \tau_x + \mu + r \cdot \sum_{d \in T_{\text{xmit}}} x^d \cdot b_d + r \cdot x^D \cdot \sum_i w_{V,i} \cdot v_{\text{blinding},i}
$$

The $\mu - \mu = 0$ cancels (the commitment-blinding contributions sum to $\mu$ by construction of $\mu$). The remaining $r$-weighted part is

$$
r \cdot \left( -\tau_x + \sum_{d \in T_{\text{xmit}}} x^d \cdot b_d + x^D \cdot \sum_i w_{V,i} \cdot v_{\text{blinding},i} \right) = 0
$$

because the prover defined $\tau_x = t_{\text{blinding}}(x) = \sum_{d \in T_{\text{xmit}}} x^d \cdot b_d + x^D \cdot \sum_i w_{V,i} \cdot v_{\text{blinding},i}$ (the $0..mid-1$ and $d \in T_{\text{xmit}}$ slots cover everything).

### Why each $G_i$ coefficient balances

For $i < n_1$ (phase 1), $u_{g,i} = 1$. The total contribution to $G_i$ is

$$
x^{mid} \cdot a_{L,i} + x^D \cdot a_{O,i} + x^{D+1} \cdot s_{L,i} + \sum_{k : i < \dim(c_{k,L})} x^{D-k} \cdot c_{k,L,i} + x^{mid} \cdot y^{-i} \cdot w_{R,i} - a \cdot s_i.
$$

The first five terms equal $\ell_i = l(x)[i]$ (by the polynomial layout). The last term is the IPP unfolding contribution. The IPP relation says $\ell_i = a \cdot s_i$ in the unscaled basis (since $G_{\text{factors}}[i] = 1$ for phase 1), so the total is zero.

For $n_1 \le i < n$ (phase 2), $u_{g,i} = u$. The vector-commitment contributions are zero (because $\dim(c_{k,L}) \le n_1$). The total is

$$
x^{mid} \cdot u \cdot a_{L,i} + x^D \cdot u \cdot a_{O,i} + x^{D+1} \cdot u \cdot s_{L,i} + u \cdot x^{mid} \cdot y^{-i} \cdot w_{R,i} - u \cdot a \cdot s_i = u \cdot (\ell_i - a \cdot s_i).
$$

The IPP relation in the scaled basis says $\ell_i = a \cdot s_i$ (when $G_{\text{factors}}[i] = u$, the $u$ cancels on both sides), so this is zero.

For $n \le i < n_{\text{pad}}$ (padding), no commitment contributes to $G_i$. The total is $u \cdot (-a \cdot s_i)$. For this to be zero, $\ell_i = 0$ for padding entries, which is exactly what the prover sets ($l_{\text{vec}}[i] = 0$ for $i \in [n, n_{\text{pad}})$).

### Why each $H_i$ coefficient balances

Same logic, symmetric. The total $H_i$ contribution for $i < n$ is

$$
u_{h,i} \cdot \left( y^{-i} \cdot (\text{comb}_i - b \cdot s_{rev,i}) - 1 \right) + (\text{commitment contributions from } A_I, S).
$$

For phase 1, the commitment contributions are $x^{mid} \cdot a_{R,i}$ (from $A_{I1}$) and $x^{D+1} \cdot s_{R,i}$ (from $S_1$). After multiplying through by $y^i$ and rearranging, the equation reduces to $r_i = b \cdot s_{\text{rev},i}$, where $r_i = r(x)[i]$ is the prover's right polynomial evaluation. This is the IPP relation.

For phase 2, scaled by $u$. Same algebraic reduction.

For padding, the equation reduces to $b \cdot s_{\text{rev},i} = -y^i$, which matches the prover's $r_{\text{vec}}[i] = -y^i$ for padding.

## Fiat-Shamir transcript

The prover and verifier append the following items to the Merlin transcript in exactly this order. Labels are byte strings.

| step | label | item | who appends |
| --- | --- | --- | --- |
| 1 | `b"dom-sep"` / `b"r1cs v1"` | r1cs domain separator | both, via `r1cs_domain_sep` |
| 2a | `b"commitment-point"` | each high-level commitment $V_i$ (in `commit` call order) | both |
| 2b | `b"vector-commitment-point"` | each vector commitment $C_k$ (in `commit_vec` call order; same label as 2a) | both |
| 3 | `b"m"` | `u64` count of $V_i$s | both |
| 4 | `b"c"` | `u64` count of vector commitments | both |
| 5 | `b"c_i"` | `u64` dimension of each vector commitment (one append per commitment) | both |
| 6 | `b"A_I1"` | $A_{I1}$ (validate non-identity on verifier side) | both |
| 7 | `b"A_O1"` | $A_{O1}$ (validate non-identity on verifier side) | both |
| 8 | `b"S1"` | $S_1$ (validate non-identity on verifier side) | both |
| 9 | `b"dom-sep"` / `b"r1cs-1phase"` or `b"r1cs-2phase"` | 1-phase or 2-phase domain separator | both |
| 10 | (randomized constraints run; any `challenge_scalar` calls inside add their own labels) | -- | both |
| 11 | `b"A_I2"` | $A_{I2}$ (identity for 1-phase) | both |
| 12 | `b"A_O2"` | $A_{O2}$ (identity for 1-phase) | both |
| 13 | `b"S2"` | $S_2$ (identity for 1-phase) | both |
| 14 | `b"y"` | sample $y$ | both |
| 15 | `b"z"` | sample $z$ | both |
| 16a | `b"t_poly degree"` | `u64` degree $d$ (one per transmitted $T_d$) | both |
| 16b | `b"t_poly"` | $T_d$ (validate non-identity on verifier side) | both |
| 17 | `b"u"` | sample $u$ (two-phase challenge) | both |
| 18 | `b"x"` | sample $x$ | both |
| 19 | `b"t_x"` | $\hat{t}$ | both |
| 20 | `b"t_x_blinding"` | $\tau_x$ | both |
| 21 | `b"e_blinding"` | $\mu$ | both |
| 22 | `b"w"` | sample $w$ for $Q = w \cdot B$ | both |
| 23 | `b"dom-sep"` / `b"ipp v1"` | IPP domain separator | both |
| 24 | `b"n"` | `u64` IPP input length $n_{\text{pad}}$ | both |
| 25a | `b"L"` | $L_j$ (validate non-identity on verifier side) -- per IPP round | both |
| 25b | `b"R"` | $R_j$ (validate non-identity on verifier side) -- per IPP round | both |
| 25c | `b"u"` | sample IPP round challenge | both |

Step 9's 1-phase vs 2-phase choice is based on whether `deferred_constraints.is_empty()` -- both sides agree because they construct the same constraint system. Step 17's $u$ is sampled regardless of whether there are phase-2 multipliers; it is only "used" if $n_2 > 0$.

The prover's transcript ordering lives in `prove_and_return_transcript_with_rng`; the verifier's mirror is in `verification_scalars_and_points_core`.

## Cross-references

The pieces described above correspond, by role, to:

- the degree-schedule helpers `degrees` / `t_poly_degree` / `committed_t_degrees`;
- the prover (polynomial construction, $T_d$ commitments, $\mu$, $\tau_x$);
- the verifier (MSM scalars and points);
- the inner-product argument (both the standalone `verify` form and the MSM form folded into the R1CS verifier);
- the batch verifier (a weighted sum of the per-proof MSMs).