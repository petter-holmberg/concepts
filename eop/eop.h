// eop.h

// Copyright (c) 2009 Alexander Stepanov and Paul McJones
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.


// Algorithms from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_EOP
#define EOP_EOP

#include "assertions.h"
#include "intrinsics.h"
#include "type_functions.h"
#include "pointers.h"
#include "integers.h"
#include "concepts.h"

#include <cstdlib> // malloc, free
#include <cmath> // sqrt


//
//  Chapter 1. Foundations
//


auto plus_0(int a, int b)
{
    return a + b;
}

auto plus_1(const int& a, const int& b)
{
    return a + b;
}

void plus_2(int* a, int* b, int* c)
{
    *c = *a + *b;
}

auto square(int n)
{
    return n * n;
}

auto square(const Domain<BinaryOperation>& x, BinaryOperation op)
{
    return op(x, x);
}


// Function object for equality

template<Regular T>
struct equal
{
    bool operator()(const T& x, const T& y)
    {
        return x == y;
    }
};

template<Regular T>
struct input_type<equal<T>, 0>
{
    using type = T;
};


// type pair (see chapter 12 of Elements of Programming)
// model Regular(Pair)

template<Regular T0, Regular T1>
struct pair
{
    T0 m0;
    T1 m1;
    pair() {} // default constructor
    pair(const T0& m0, const T1& m1) : m0{m0}, m1{m1} {}
};

template<Regular T0, Regular T1>
struct underlying_type<pair<T0, T1>>
{
    using type = pair<UnderlyingType<T0>, UnderlyingType<T1>>;
};

template<Regular T0, Regular T1>
bool operator==(const pair<T0, T1>& x, const pair<T0, T1>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1;
}

template<TotallyOrdered T0, TotallyOrdered T1>
bool operator<(const pair<T0, T1>& x, const pair<T0, T1>& y)
{
    return x.m0 < y.m0 || (!(y.m0 < x.m0) && x.m1 < y.m1);
}


// type triple (see Exercise 12.2 of Elements of Programming)
// model Regular(triple)

template<Regular T0, Regular T1, Regular T2>
struct triple
{
    T0 m0;
    T1 m1;
    T2 m2;
    triple() {}
    triple(T0 m0, T1 m1, T2 m2) : m0{m0}, m1{m1}, m2{m2} {}
};

template<Regular T0, Regular T1, Regular T2>
struct underlying_type<triple<T0, T1, T2>>
{
    using type = triple<UnderlyingType<T0>, UnderlyingType<T1>, UnderlyingType<T2>>;
};

template<Regular T0, Regular T1, Regular T2>
bool operator==(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1 && x.m2 == y.m2;
}

template<Regular T0, Regular T1, Regular T2>
bool operator<(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return
        x.m0 < y.m0 ||
        (!(y.m0 < x.m0) && x.m1 < y.m1) ||
        (!(y.m1 < x.m1) && x.m2 < y.m2);
}


//
//  Chapter 2. Transformations and their orbits
//


//int abs(int x) {
//    if (x < 0) return -x; else return x;
//} // unary operation

auto euclidean_norm(double x, double y)
{
    return sqrt(x * x + y * y);
} // binary operation

auto euclidean_norm(double x, double y, double z)
{
    return sqrt(x * x + y * y + z * z);
} // ternary operation

template<Transformation F>
auto power_unary(Domain<F> x, Integer n, F f)
{
    // Precondition:
    // $n \geq 0 \wedge (\forall i \in N)\,0 < i \leq n \Rightarrow f^i(x)$ is defined
    using N = decltype(n);
    while (n != N{0}) {
        n = n - N{1};
        x = f(x);
    }
    return x;
}

template<Transformation F>
auto distance(Domain<F> x, Domain<F> y, F f)
{
    // Precondition: $y$ is reachable from $x$ under $f$
    using N = DistanceType<F>;
    N n{0};
    while (x != y) {
        x = f(x);
        n = n + N{1};
    }
    return n;
}

template<Transformation F, UnaryPredicate P>
auto collision_point(const Domain<F>& x, F f, P p)
    __requires(Domain<F> == Domain<P>)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    if (!p(x)) return x;
    Domain<F> slow = x;            // $slow = f^0(x)$
    Domain<F> fast = f(x);         // $fast = f^1(x)$
                                   // $n \gets 0$ (completed iterations)
    while (fast != slow) {         // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow);            // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        if (!p(fast)) return fast;
        fast = f(fast);            // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        if (!p(fast)) return fast;
        fast = f(fast);            // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                                   // $n \gets n + 1$
    }
    return fast;                   // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
    // Postcondition: return value is terminal point or collision point
}

template<Transformation F, UnaryPredicate P>
bool terminating(const Domain<F>& x, F f, P p)
    requires Same<Domain<F>, Domain<P>>()
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    return !p(collision_point(x, f, p));
}

template<Transformation F>
auto collision_point_nonterminating_orbit(const Domain<F>& x, F f)
{
    Domain<F> slow = x;        // $slow = f^0(x)$
    Domain<F> fast = f(x);     // $fast = f^1(x)$
                               // $n \gets 0$ (completed iterations)
    while (fast != slow) {     // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                               // $n \gets n + 1$
    }
    return fast;               // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
    // Postcondition: return value is collision point
}

template<Transformation F>
bool circular_nonterminating_orbit(const Domain<F>& x, F f)
{
    return x == f(collision_point_nonterminating_orbit(x, f));
}

template<Transformation F, UnaryPredicate P>
bool circular(const Domain<F>& x, F f, P p)
    requires Same<Domain<F>, Domain<P>>()
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    Domain<F> y = collision_point(x, f, p);
    return p(y) && x == f(y);
}

template<Transformation F>
auto convergent_point(Domain<F> x0, Domain<F> x1, F f)
{
    // Precondition: $(\exists n \in \func{DistanceType}(F))\,n \geq 0 \wedge f^n(x0) = f^n(x1)$
    while (x0 != x1) {
        x0 = f(x0);
        x1 = f(x1);
    }
    return x0;
}

template<Transformation F>
auto connection_point_nonterminating_orbit(const Domain<F>& x, F f)
{
    return convergent_point(
        x, f(collision_point_nonterminating_orbit(x, f)), f
    );
}

template<Transformation F, UnaryPredicate P>
auto connection_point(const Domain<F>& x, F f, P p)
    __requires(Domain<F> == Domain<P>)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    auto y = collision_point(x, f, p);
    if (!p(y)) return y;
    return convergent_point(x, f(y), f);
}

// Exercise 2.3:

template<Transformation F>
auto convergent_point_guarded(Domain<F> x0, Domain<F> x1, Domain<F> y, F f)
{
    // Precondition: $\func{reachable}(x0, y, f) \wedge \func{reachable}(x1, y, f)$
    using N = DistanceType<F>;
    N d0 = distance(x0, y, f);
    N d1 = distance(x1, y, f);
    if (d0 < d1)
        x1 = power_unary(x1, d1 - d0, f);
    else if (d1 < d0)
        x0 = power_unary(x0, d0 - d1, f);
    return convergent_point(x0, x1, f);
}

template<Transformation F>
auto orbit_structure_nonterminating_orbit(const Domain<F>& x, F f)
{
    auto y = connection_point_nonterminating_orbit(x, f);
    return triple<DistanceType<F>, DistanceType<F>, Domain<F>>{
        distance(x, y, f), distance(f(y), y, f), y
    };
}

template<Transformation F>
auto orbit_structure(const Domain<F>& x, F f, UnaryPredicate p)
    __requires(Domain<F> == Domain<P>)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    using N = DistanceType<F>;
    auto y = connection_point(x, f, p);
    N m = distance(x, y, f);
    N n{0};
    if (p(y)) n = distance(f(y), y, f);
    // Terminating: $m = h - 1 \wedge n = 0$
    // Otherwise:   $m = h \wedge n = c - 1$
    return triple<N, N, Domain<F>>{m, n, y};
}


//
//  Chapter 3. Associative operations
//


template<Integer I, BinaryOperation Op>
auto power_left_associated(Domain<Op> a, I n, Op op)
{
    // Precondition: $n > 0$
    if (n == I{1}) return a;
    return op(power_left_associated(a, n - I{1}, op), a);
}

template<Integer I, BinaryOperation Op>
auto power_right_associated(Domain<Op> a, I n, Op op)
{
    // Precondition: $n > 0$
    if (n == I{1}) return a;
    return op(a, power_right_associated(a, n - I{1}, op));
}

template<Integer I, BinaryOperation Op>
auto power_0(Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if (n == I{1}) return a;
    if (n % I{2} == I{0}) return power_0(op(a, a), n / I{2}, op);
    return op(power_0(op(a, a), n / I{2}, op), a);
}

template<Integer I, BinaryOperation Op>
auto power_1(Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if (n == I{1}) return a;
    auto r = power_1(op(a, a), n / I{2}, op);
    if (n % I{2} != I{0}) r = op(r, a);
    return r;
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_0(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I{0}) return r;
    if (n % I{2} != I{0}) r = op(r, a);
    return power_accumulate_0(r, op(a, a), n / I{2}, op);
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_1(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I{0}) return r;
    if (n == I{1}) return op(r, a);
    if (n % I{2} != I{0}) r = op(r, a);
    return power_accumulate_1(r, op(a, a), n / I{2}, op);
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_2(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n % I{2} != I{0}) {
        r = op(r, a);
        if (n == I{1}) return r;
    } else if (n == I{0}) return r;
    return power_accumulate_2(r, op(a, a), n / I{2}, op);
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_3(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n % I{2} != I{0}) {
        r = op(r, a);
        if (n == I{1}) return r;
    } else if (n == I{0}) return r;
    a = op(a, a);
    n = n / I{2};
    return power_accumulate_3(r, a, n, op);
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_4(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    while (true) {
        if (n % I{2} != I{0}) {
            r = op(r, a);
            if (n == I{1}) return r;
        } else if (n == I{0}) return r;
        a = op(a, a);
        n = n / I{2};
    }
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_positive_0(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    while (true) {
        if (n % I{2} != I{0}) {
            r = op(r, a);
            if (n == I{1}) return r;
        }
        a = op(a, a);
        n = n / I{2};
    }
}

template<Integer I, BinaryOperation Op>
auto power_accumulate_5(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I{0}) return r;
    return power_accumulate_positive_0(r, a, n, op);
}

template<Integer I, BinaryOperation Op>
auto power_2(Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    return power_accumulate_5(a, a, n - I{1}, op);
}

template<Integer I, BinaryOperation Op>
auto power_3(Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    while (n % I{2} == I{0}) {
        a = op(a, a);
        n = n / I{2};
    }
    n = n / I{2};
    if (n == I{0}) return a;
    return power_accumulate_positive_0(a, op(a, a), n, op);
}


template<Integer I, BinaryOperation Op>
auto power_accumulate_positive(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    while (true) {
      if (odd(n)) {
          r = op(r, a);
          if (one(n)) return r;
      }
      a = op(a, a);
      n = half_nonnegative(n);
    }
}

template<Integer I, BinaryOperation Op>
auto power_accumulate(Domain<Op> r, Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if (zero(n)) return r;
    return power_accumulate_positive(r, a, n, op);
}

template<Integer I, BinaryOperation Op>
auto power(Domain<Op> a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    while (even(n)) {
        a = op(a, a);
        n = half_nonnegative(n);
    }
    n = half_nonnegative(n);
    if (zero(n)) return a;
    return power_accumulate_positive(a, op(a, a), n, op);
}

template<Integer I, BinaryOperation Op>
auto power(Domain<Op> a, I n, Op op, Domain<Op> id)
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if (zero(n)) return id;
    return power(a, n, op);
}

template<Integer I>
auto fibonacci_matrix_multiply(const pair<I, I>& x, const pair<I, I>& y) -> pair<I, I>
{
    return {x.m0 * (y.m1 + y.m0) + x.m1 * y.m0, x.m0 * y.m0 + x.m1 * y.m1};
}

auto fibonacci(Integer n)
{
    // Precondition: $n \geq 0$
    using I = decltype(n);
    if (n == I{0}) return I{0};
    return power({I{1}, I{0}}, n, fibonacci_matrix_multiply<I>).m0;
}


//
//  Chapter 4. Linear orderings
//


// Exercise 4.1: Give an example of a relation that is neither strict nor reflexive
// Exercise 4.2: Give an example of a symmetric relation that is not transitive
// Exercise 4.3: Give an example of a symmetric relation that is not reflexive


template<Relation R>
struct complement
{
    R r;
    complement(R r) : r{r} {}
    bool operator()(const Domain<R>& x, const Domain<R>& y) {
        return !r(x, y);
    }
};

template<Relation R>
struct input_type<complement<R>, 0>
{
    using type = Domain<R>;
};

template<Relation R>
struct converse
{
    R r;
    converse(R r) : r{r} {}
    bool operator()(const Domain<R>& x, const Domain<R>& y)
    {
        return r(y, x);
    }
};

template<Relation R>
struct input_type<converse<R>, 0>
{
    using type = Domain<R>;
};

template<Relation R>
struct complement_of_converse
{
    using T = Domain<R>;
    R r;
    complement_of_converse(const R& r) : r{r} {}
    bool operator()(const T& a, const T& b)
    {
        return !r(b, a);
    }
};

template<Relation R>
struct input_type<complement_of_converse<R>, 0>
{
    using type = Domain<R>;
};

template<Relation R>
struct symmetric_complement
{
    R r;
    symmetric_complement(R r) : r{r} {}
    bool operator()(const Domain<R>& a, const Domain<R>& b)
    {
        return !r(a, b) && !r(b, a);
    }
};

template<Relation R>
struct input_type<symmetric_complement<R>, 0>
{
    using type = Domain<R>;
};

template<Relation R>
auto select_0_2(const Domain<R>& a, const Domain<R>& b, R r) -> const Domain<R>&
{
    // Precondition: $\func{weak\_ordering}(r)$
    if (r(b, a)) return b;
    return a;
}

template<Relation R>
auto select_1_2(const Domain<R>& a, const Domain<R>& b, R r) -> const Domain<R>&
{
    // Precondition: $\func{weak\_ordering}(r)$
    if (r(b, a)) return a;
    return b;
}

template<Relation R>
auto select_0_3(
    const Domain<R>& a, const Domain<R>& b, const Domain<R>& c, R r
) -> const Domain<R>&
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<Relation R>
auto select_2_3(
    const Domain<R>& a, const Domain<R>& b, const Domain<R>& c, R r
) -> const Domain<R>&
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<Relation R>
auto select_1_3_ab(
    const Domain<R>& a, const Domain<R>& b, const Domain<R>& c, R r
) -> const Domain<R>&
{
    if (!r(c, b)) return b;     // $a$, $b$, $c$ are sorted
    return select_1_2(a, c, r); // $b$ is not the median
}

template<Relation R>
auto select_1_3(
    const Domain<R>& a, const Domain<R>& b, const Domain<R>& c, R r
) -> const Domain<R>&
{
    if (r(b, a)) return
        select_1_3_ab(b, a, c, r);
    return
        select_1_3_ab(a, b, c, r);
}

template<Relation R>
auto select_1_4_ab_cd(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    if (r(c, a)) return
        select_0_2(a, d, r);
    return
        select_0_2(b, c, r);
}

template<Relation R>
auto select_1_4_ab(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    if (r(d, c)) return
        select_1_4_ab_cd(a, b, d, c, r);
    return
        select_1_4_ab_cd(a, b, c, d, r);
}

template<Relation R>
auto select_1_4(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    if (r(b, a)) return
        select_1_4_ab(b, a, c, d, r);
    return
        select_1_4_ab(a, b, c, d, r);
}

// Exercise 4.4: select_2_4


// Order selection procedures with stability indices

template<bool strict, Relation R>
struct compare_strict_or_reflexive;

template<Relation R>
struct compare_strict_or_reflexive<true, R> // strict
{
    bool operator()(const Domain<R>& a, const Domain<R>& b, R r)
    {
        return r(a, b);
    }
};

template<Relation R>
struct compare_strict_or_reflexive<false, R> // reflexive
{
    bool operator()(const Domain<R>& a, const Domain<R>& b, R r)
    {
        return !r(b, a); // $\func{complement\_of\_converse}_r(a, b)$
    }
};

template<int ia, int ib, Relation R>
auto select_0_2(const Domain<R>& a, const Domain<R>& b, R r) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return b;
    return a;
}

template<int ia, int ib, Relation R>
auto select_1_2(const Domain<R>& a, const Domain<R>& b, R r) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return a;
    return b;
}

template<int ia, int ib, int ic, int id, Relation R>
auto select_1_4_ab_cd(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_0_2<ia,id>(a, d, r);
    return
        select_0_2<ib,ic>(b, c, r);
}

template<int ia, int ib, int ic, int id, Relation R>
auto select_1_4_ab(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_1_4_ab_cd<ia,ib,id,ic>(a, b, d, c, r);
    return
        select_1_4_ab_cd<ia,ib,ic,id>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, Relation R>
auto select_1_4(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_1_4_ab<ib,ia,ic,id>(b, a, c, d, r);
    return
        select_1_4_ab<ia,ib,ic,id>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, int ie, Relation R>
auto select_2_5_ab_cd(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    const Domain<R>& e,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_1_4_ab<ia,ib,id,ie>(a, b, d, e, r);
    return
        select_1_4_ab<ic,id,ib,ie>(c, d, b, e, r);
}

template<int ia, int ib, int ic, int id, int ie, Relation R>
auto select_2_5_ab(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    const Domain<R>& e,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_2_5_ab_cd<ia,ib,id,ic,ie>(a, b, d, c, e, r);
    return
        select_2_5_ab_cd<ia,ib,ic,id,ie>(a, b, c, d, e, r);
}

template<int ia, int ib, int ic, int id, int ie, Relation R>
auto select_2_5(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    const Domain<R>& e,
    R r
) -> const Domain<R>&
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_2_5_ab<ib,ia,ic,id,ie>(b, a, c, d, e, r);
    return
        select_2_5_ab<ia,ib,ic,id,ie>(a, b, c, d, e, r);
}

// Exercise 4.5. Find an algorithm for median of 5 that does slightly fewer comparisons
// on average


template<Relation R>
auto median_5(
    const Domain<R>& a,
    const Domain<R>& b,
    const Domain<R>& c,
    const Domain<R>& d,
    const Domain<R>& e,
    R r
) -> const Domain<R>&
{
    return select_2_5<0,1,2,3,4>(a, b, c, d, e, r);
}


// Exercise 4.6. Prove the stability of every order selection procedure in this section
// Exercise 4.7. Verify the correctness and stability of every order selection procedure
// in this section by exhaustive testing


// Natural total ordering

template<TotallyOrdered T>
struct less
{
    bool operator()(const T& x, const T& y)
    {
        return x < y;
    }
};

template<TotallyOrdered T>
struct input_type<less<T>, 0>
{
    using type = T;
};

template<TotallyOrdered T>
auto min(const T& a, const T& b)
{
    return select_0_2(a, b, less<T>());
}

template<TotallyOrdered T>
auto max(const T& a, const T& b)
{
    return select_1_2(a, b, less<T>());
}


// Clusters of related procedures: equality and ordering

bool operator!=(const Regular& x, const Regular& y)
{
    return !(x==y);
}

bool operator>(const TotallyOrdered& x, const TotallyOrdered& y)
{
    return y < x;
}

bool operator<=(const TotallyOrdered& x, const TotallyOrdered& y)
{
    return !(y < x);
}

bool operator>=(const TotallyOrdered& x, const TotallyOrdered& y)
{
    return !(x < y);
}


// Exercise 4.8: Rewrite the algorithms in this chapter using three-valued comparison


//
//  Chapter 5. Ordered algebraic structures
//


template<AdditiveSemigroup T>
struct plus
{
    auto operator()(const T& x, const T& y)
    {
        return x + y;
    }
};

template<AdditiveSemigroup T>
struct input_type<plus<T>, 0>
{
    using type = T;
};

template<MultiplicativeSemigroup T>
struct multiplies
{
    auto operator()(const T& x, const T& y)
    {
        return x * y;
    }
};

template<MultiplicativeSemigroup T>
struct input_type<multiplies<T>, 0>
{
    using type = T;
};

template<typename Op>
    __requires(SemigroupOperation(Op)) // ***** or MultiplicativeSemigroup ?????
struct multiplies_transformation
{
    Domain<Op> x;
    Op op;
    multiplies_transformation(Domain<Op> x, Op op) : x(x), op(op) {}
    auto operator()(const Domain<Op>& y)
    {
        return op(x, y);
    }
};

template<typename Op>
   __requires(SemigroupOperation(Op))
struct input_type<multiplies_transformation<Op>, 0>
{
    using type = Domain<Op>;
};

template<AdditiveGroup T>
struct negate
{
    auto operator()(const T& x)
    {
        return -x;
    }
};

template<AdditiveGroup T>
struct input_type<negate<T>, 0>
{
    using type = T;
};

auto abs(const OrderedAdditiveGroup& a)
{
    if (a < decltype(a){0}) return -a;
    else return a;
}

auto slow_remainder(CancellableMonoid a, CancellableMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    while (b <= a) a = a - b;
    return a;
}

auto slow_quotient(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    QuotientType<decltype(a)> n{0};
    while (b <= a) {
        a = a - b;
        n = successor(n);
    }
    return n;
}

template<ArchimedeanMonoid T>
auto remainder_recursive(T a, T b) -> T
{
    // Precondition: $a \geq b > 0$
    if (a - b >= b) {
        a = remainder_recursive(a, b + b);
        if (a < b) return a;
    }
    return a - b;
}

auto remainder_nonnegative(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    return remainder_recursive(a, b);
}

/* The next function is due to:
    Robert W. Floyd and Donald E. Knuth.
    Addition machines.
    \emph{SIAM Journal on Computing},
    Volume 19, Number 2, 1990, pages 329--340.
*/

auto remainder_nonnegative_fibonacci(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    auto c = b;
    do {
        auto tmp = c;
        c = b + c;
        b = tmp;
    } while (a >= c);
    do {
        if (a >= b) a = a - b;
        auto tmp = c - b;
        c = b;
        b = tmp;
    } while (b < c);
    return a;
}

auto largest_doubling(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq b > 0$
    while (b <= a - b) b = b + b;
    return b;
}

auto remainder_nonnegative_iterative(HalvableMonoid a, HalvableMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    auto c = largest_doubling(a, b);
    a = a - c;
    while (c != b) {
        c = half(c);
        if (c <= a) a = a - c;
    }
    return a;
}

// Jon Brandt suggested this algorithm (it is not mentioned in chapter 5):

auto remainder_nonnegative_with_largest_doubling(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq T(0) \wedge b > T(0)$
    while (b <= a)
        a = a - largest_doubling(a, b);
    return a;
}

auto subtractive_gcd_nonzero(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a > 0 \wedge b > 0$
    while (true) {
        if (b < a)
            a = a - b;
        else if (a < b)
            b = b - a;
        else
            return a;
    }
}

auto subtractive_gcd(EuclideanMonoid a, EuclideanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    using T = decltype(a);
    while (true) {
        if (b == T{0}) return a;
        while (b <= a) a = a - b;
        if (a == T{0}) return b;
        while (a <= b) b = b - a;
    }
}

auto fast_subtractive_gcd(EuclideanMonoid a, EuclideanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    using T = decltype(a);
    while (true) {
        if (b == T{0}) return a;
        a = remainder_nonnegative(a, b);
        if (a == T{0}) return b;
        b = remainder_nonnegative(b, a);
    }
}

auto gcd(EuclideanSemiring a, EuclideanSemiring b)
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    using T = decltype(a);
    while (true) {
        if (b == T{0}) return a;
        a = remainder(a, b);
        if (a == T{0}) return b;
        b = remainder(b, a);
    }
}

template<typename T, typename S>
auto gcd(T a, T b)
    requires EuclideanSemimodule<T, S>()
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    while (true) {
        if (b == T{0}) return a;
        a = remainder(a, b);
        if (a == T{0}) return b;
        b = remainder(b, a);
    }
}


// Exercise 5.3:

auto stein_gcd_nonnegative(Integer a, Integer b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    if (zero(a)) return b;
    if (zero(b)) return a;
    int d = 0;
    while (even(a) && even(b)) {
        a = half_nonnegative(a);
        b = half_nonnegative(b);
        d = d + 1;
    }
    while (even(a)) a = half_nonnegative(a);
    while (even(b)) b = half_nonnegative(b);
    while (true)
        if (a < b) {
            b = b - a;
            do { b = half_nonnegative(b); } while (even(b));
        } else if (b < a) {
            a = a - b;
            do { a = half_nonnegative(a); } while (even(a));
        } else return binary_scale_up_nonnegative(a, d);
}

auto quotient_remainder_nonnegative(ArchimedeanMonoid a, ArchimedeanMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    using T = decltype(a);
    using N = QuotientType<T>;
    using NT = pair<N, T>;
    if (a < b) return NT{N{0}, a};
    if (a - b < b) return NT{N{1}, a - b};
    auto q = quotient_remainder_nonnegative(a, b + b);
    auto m = twice(q.m0);
    a = q.m1;
    if (a < b)
        return NT{m, a};
    else
        return NT{successor(m), a - b};
}

auto quotient_remainder_nonnegative_iterative(HalvableMonoid a, HalvableMonoid b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    using T = decltype(a);
    using N = QuotientType<T>;
    using NT = pair<N, T>;
    if (a < b) return NT{N{0}, a};
    auto c = largest_doubling(a, b);
    a = a - c;
    N n{1};
    while (c != b) {
        n = twice(n);
        c = half(c);
        if (c <= a) {
            a = a - c;
            n = successor(n);
        }
    }
    return NT{n, a};
}

template<typename Op>
auto remainder(Domain<Op> a, Domain<Op> b, Op rem)
    requires BinaryOperation<Op>() && ArchimedeanGroup<Domain<Op>>()
{
    // Precondition: $b \neq 0$
    using T = decltype(a);
    T r;
    if (a < T{0})
        if (b < T{0}) {
            r = -rem(-a, -b);
        } else {
            r =  rem(-a,  b); if (r != T{0}) r = b - r;
        }
    else
        if (b < T{0}) {
            r =  rem(a, -b);  if (r != T{0}) r = b + r;
        } else {
            r =  rem(a,  b);
        }
    return r;
}

template<HomogeneousFunction F>
auto quotient_remainder(Domain<F> a, Domain<F> b, F quo_rem)
    requires ArchimedeanGroup<Domain<F>>() && Arity<F> == 2
    __requires(Codomain<F> == pair<QuotientType<Domain<F>>, Domain<F>>)
{
    // Precondition: $b \neq 0$
    using T = decltype(a);
    pair<QuotientType<T>, T> q_r;
    if (a < T{0}) {
        if (b < T{0}) {
            q_r = quo_rem(-a, -b); q_r.m1 = -q_r.m1;
        } else {
            q_r = quo_rem(-a, b);
            if (q_r.m1 != T{0}) {
                q_r.m1 = b - q_r.m1; q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = -q_r.m0;
        }
    } else {
        if (b < T{0}) {
            q_r = quo_rem(a, -b);
            if (q_r.m1 != T{0}) {
                q_r.m1 = b + q_r.m1; q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = -q_r.m0;
        }
        else
            q_r = quo_rem(a, b);
    }
    return q_r;
}


//
//  Chapter 6. Iterators
//


void increment(Iterator& x)
{
    // Precondition: $\func{successor}(x)$ is defined
    x = successor(x);
}


auto operator+(Iterator f, DistanceType<Iterator> n)
{
    // Precondition: $n \geq 0 \wedge \property{weak\_range}(f, n)$
    while (!zero(n)) {
        n = predecessor(n);
        f = successor(f);
    }
    return f;
}


auto operator-(Iterator l, Iterator f)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    DistanceType<decltype(l)> n{0};
    while (f != l) {
        n = successor(n);
        f = successor(f);
    }
    return n;
}

template<typename I>
concept bool ReadableIterator = requires { Readable<I>() && Iterator<I>(); };

template<typename I, typename Proc>
auto for_each(I f, I l, Proc proc)
    requires ReadableIterator<I> && Arity<Proc> == 1
    __requires(Procedure(Proc) && ValueType<I> == InputType<Proc, 0>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        proc(source(f));
        f = successor(f);
    }
    return proc;
}

template<typename I>
auto find(I f, I l, const ValueType<I>& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && source(f) != x) f = successor(f);
    return f;
}

template<typename I>
auto find_not(I f, I l, const ValueType<I>& x)
    requires ReadableIterator<I>
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && source(f) == x) f = successor(f);
    return f;
}

auto find_if(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && !p(source(f))) f = successor(f);
    return f;
}

auto find_if_not(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && p(source(f))) f = successor(f);
    return f;
}

// Exercise 6.1: quantifier functions

bool all(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if_not(f, l, p);
}

bool none(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if(f, l, p);
}

bool not_all(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return !all(f, l, p);
}

bool some(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return !none(f, l, p);
}

auto count_if(ReadableIterator f, ReadableIterator l, UnaryPredicate p, Iterator j)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}


// Exercise 6.2: implement count_if using for_each


auto count_if(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(f)>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count_if(f, l, p, DistanceType<decltype(f)>{0});
}

template<ReadableIterator I>
auto count(I f, I l, const ValueType<I>& x, Iterator j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) == x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<ReadableIterator I>
auto count(I f, I l, const ValueType<I>& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count(f, l, x, DistanceType<I>{0});
}

template<ReadableIterator I>
auto count_not(I f, I l, const ValueType<I>& x, Iterator j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) != x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<ReadableIterator I>
auto count_not(I f, I l, const ValueType<I>& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count_not(f, l, x, DistanceType<I>{0});
}

auto count_if_not(ReadableIterator f, ReadableIterator l, UnaryPredicate p, Iterator j)
    requires Same<Domain<decltype(p)>, ValueType<decltype(f)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (!p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}

auto count_if_not(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    requires Same<Domain<decltype(p)>, ValueType<decltype(f)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count_if_not(f, l, p, DistanceType<decltype(f)>{0});
}

template<typename I, typename Op, UnaryFunction F>
auto reduce_nonempty(I f, I l, Op op, F fun)
    requires Iterator<I>() && BinaryOperation<Op>()
    __requires(I == Domain<F> && Codomain<F> == Domain<Op>)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    auto r = fun(f);
    f = successor(f);
    while (f != l) {
        r = op(r, fun(f));
        f = successor(f);
    }
    return r;
}

auto reduce_nonempty(ReadableIterator f, ReadableIterator l, BinaryOperation op)
    requires Same<ValueType<decltype(f)>, Domain<decltype(op)>>()
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    auto r = source(f);
    f = successor(f);
    while (f != l) {
        r = op(r, source(f));
        f = successor(f);
    }
    return r;
}

template<BinaryOperation Op>
auto reduce(Iterator f, Iterator l, Op op, UnaryFunction fun, const Domain<Op>& z)
    requires Same<decltype(f), Domain<decltype(fun)>>()
    __requires(Codomain<decltype(fun)> == Domain<Op>)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    if (f == l) return z;
    return reduce_nonempty(f, l, op, fun);
}

template<BinaryOperation Op>
auto reduce(Iterator f, Iterator l, Op op, const Domain<Op>& z)
    requires Same<ValueType<decltype(f)>, Domain<Op>>()
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    if (f == l) return z;
    return reduce_nonempty(f, l, op);
}

template<BinaryOperation Op>
auto reduce_nonzeroes(Iterator f, Iterator l, Op op, UnaryFunction fun, const Domain<Op>& z)
    requires Same<decltype(f), Domain<decltype(fun)>>()
    __requires(I == Domain<decltype(fun)> && Codomain<F> == Domain<Op>)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    Domain<Op> x;
    do {
        if (f == l) return z;
        x = fun(f);
        f = successor(f);
    } while (x == z);
    while (f != l) {
        Domain<Op> y = fun(f);
        if (y != z) x = op(x, y);
        f = successor(f);
    }
    return x;
}

template<BinaryOperation Op>
auto reduce_nonzeroes(Iterator f, Iterator l, Op op, const Domain<Op>& z)
    requires Same<ValueType<decltype(f)>, Domain<Op>>()
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    Domain<Op> x;
    do {
        if (f == l) return z;
        x = source(f);
        f = successor(f);
    } while (x == z);
    while (f != l) {
        auto y = source(f);
        if (y != z) x = op(x, y);
        f = successor(f);
    }
    return x;
}

auto reduce(ReadableIterator f, ReadableIterator l)
    requires AdditiveMonoid<ValueType<decltype(f)>>()
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    using T = ValueType<decltype(f)>;
    return reduce(f, l, plus<T>(), T{0});
}

template<ReadableIterator I, typename Proc>
auto for_each_n(I f, DistanceType<I> n, Proc proc)
    requires Arity<Proc> == 1
    __requires(Procedure(Proc) && ValueType<I> == InputType<Proc, 0>)
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while (!zero(n)) {
        n = predecessor(n);
        proc(source(f));
        f = successor(f);
    }
    return pair<Proc, I>{proc, f};
}

template<ReadableIterator I>
auto find_n(I f, DistanceType<I> n, const ValueType<I>& x)
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while (!zero(n) && source(f) != x) {
        n = predecessor(n);
        f = successor(f);
    }
    return pair<I, DistanceType<I>>{f, n};
}


// Exercise 6.3: implement variations taking a weak range instead of a bounded range
// of all the versions of find, quantifiers, count, and reduce


auto find_if_unguarded(ReadableIterator f, UnaryPredicate p)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition:
    // $(\exists l)\,\func{readable\_bounded\_range}(f, l) \wedge \func{some}(f, l, p)$
    while (!p(source(f))) f = successor(f);
    return f;
    // Postcondition: $p(\func{source}(f))$
}

auto find_if_not_unguarded(ReadableIterator f, UnaryPredicate p)
    __requires(Domain<declype(f)> == ValueType<decltype(p)>)
{
    // Let $l$ be the end of the implied range starting with $f$
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{not\_all}(f, l, p)$
    while (p(source(f))) f = successor(f);
    return f;
}

template<ReadableIterator I0, ReadableIterator I1>
auto find_mismatch(I0 f0, I0 l0, I1 f1, I1 l1, Relation r)
    __requires(ValueType<I0> == ValueType<I1> && ValueType<I0> == Domain<decltype(r)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\func{readable\_bounded\_range}(f1, l1)$
    while (f0 != l0 && f1 != l1 && r(source(f0), source(f1))) {
        f0 = successor(f0);
        f1 = successor(f1);
    }
    return pair<I0, I1>{f0, f1};
}

auto find_adjacent_mismatch(ReadableIterator f, ReadableIterator l, Relation r)
    __requires(ValueType<decltype(f)> == Domain<decltype(r)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if (f == l) return l;
    auto x = source(f);
    f = successor(f);
    while (f != l && r(x, source(f))) {
        x = source(f);
        f = successor(f);
    }
    return f;
}

bool relation_preserving(ReadableIterator f, ReadableIterator l, Relation r)
    __requires(ValueType<decltype(f)> == Domain<decltype(r)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_adjacent_mismatch(f, l, r);
}

bool strictly_increasing_range(ReadableIterator f, ReadableIterator l, Relation r)
    __requires(ValueType<decltype(f)> == Domain<decltype(r)>)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    return relation_preserving(f, l, r);
}

bool increasing_range(ReadableIterator f, ReadableIterator l, Relation r)
    __requires(ValueType<decltype(f)> == Domain<decltype(r)>)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    return relation_preserving(f, l, complement_of_converse<decltype(r)>(r));
}

bool partitioned(ReadableIterator f, ReadableIterator l, UnaryPredicate p)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if_not(find_if(f, l, p), l, p);
}


// Exercise 6.6: partitioned_n


template<typename I>
concept bool ReadableForwardIterator = requires { Readable<I>() && ForwardIterator<I>(); };

template<ReadableForwardIterator I>
auto find_adjacent_mismatch_forward(I f, I l, Relation r)
    requires Same<ValueType<I>, Domain<decltype(r)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if (f == l) return l;
    I t;
    do {
        t = f;
        f = successor(f);
    } while (f != l && r(source(t), source(f)));
    return f;
}

template<ReadableForwardIterator I>
auto partition_point_n(I f, DistanceType<I> n, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition:
    // $\func{readable\_counted\_range}(f, n) \wedge \func{partitioned\_n}(f, n, p)$
    while (!zero(n)) {
        auto h = half_nonnegative(n);
        auto m = f + h;
        if (p(source(m))) {
            n = h;
        } else {
            n = n - successor(h); f = successor(m);
        }
    }
    return f;
}

template<ReadableForwardIterator I>
auto partition_point(I f, I l, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{partitioned}(f, l, p)$
    return partition_point_n(f, l - f, p);
}

template<Relation R>
struct lower_bound_predicate
{
    using T = Domain<R>;
    const T& a;
    R r;
    lower_bound_predicate(const T& a, R r) : a{a}, r{r} {}
    bool operator()(const T& x) { return !r(x, a); }
};

template<ReadableForwardIterator I>
auto lower_bound_n(I f, DistanceType<I> n, const ValueType<I>& a, Relation r)
    requires Same<ValueType<I>, Domain<decltype(r)>>()
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    lower_bound_predicate<decltype(r)> p{a, r};
    return partition_point_n(f, n, p);
}

template<Relation R>
struct upper_bound_predicate
{
    using T = Domain<R>;
    const T& a;
    R r;
    upper_bound_predicate(const T& a, R r) : a{a}, r{r} {}
    bool operator()(const T& x) { return r(a, x); }
};

template<ReadableForwardIterator I>
auto upper_bound_n(I f, DistanceType<I> n, const ValueType<I>& a, Relation r)
    requires Same<ValueType<I>, Domain<decltype(r)>>()
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    upper_bound_predicate<decltype(r)> p{a, r};
    return partition_point_n(f, n, p);
}


// Exercise 6.7: equal_range


template<BidirectionalIterator I>
auto operator-(I l, DistanceType<I> n)
{
    // Precondition: $n \geq 0 \wedge (\exists f \in I)\,(\func{weak\_range}(f, n) \wedge l = f+n)$
    while (!zero(n)) {
        n = predecessor(n);
        l = predecessor(l);
    }
    return l;
}

template<typename I>
concept bool ReadableBidirectionalIterator = requires { Readable<I>() && BidirectionalIterator<I>(); };

template<ReadableBidirectionalIterator I>
auto find_backward_if(I f, I l, UnaryPredicate p)
    requires Same<ValueType<I>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (l != f && !p(source(predecessor(l))))
        l = predecessor(l);
    return l;
}

template<ReadableBidirectionalIterator I>
auto find_backward_if_not(I f, I l, UnaryPredicate p)
    requires Same<ValueType<I>, Domain<decltype(p)>>()
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (l != f && p(source(predecessor(l))))
        l = predecessor(l);
    return l;
}


// Exercise 6.8: optimized find_backward_if


// Exercise 6.9: palindrome predicate


auto find_backward_if_unguarded(ReadableBidirectionalIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(l)>, Domain<decltype(p)>>()
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{some}(f, l, p)$
    do l = predecessor(l); while (!p(source(l)));
    return l;
    // Postcondition: $p(\func{source}(l))$
}

auto find_backward_if_not_unguarded(ReadableBidirectionalIterator l, UnaryPredicate p)
    requires Same<ValueType<decltype(l)>, Domain<decltype(p)>>()
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{not\_all}(f, l, p)$
    do l = predecessor(l); while (p(source(l)));
    return l;
    // Postcondition: $\neg p(\func{source}(l))$
}


//
//  Chapter 7. Coordinate structures
//


auto weight_recursive(BifurcateCoordinate c)
{
    // Precondition: $\property{tree}(c)$
    using N = WeightType<decltype(c)>;
    if (empty(c)) return N{0};
    N l{0};
    N r{0};
    if (has_left_successor(c))
        l = weight_recursive(left_successor(c));
    if (has_right_successor(c))
        r = weight_recursive(right_successor(c));
    return successor(l + r);
}

auto height_recursive(BifurcateCoordinate c)
{
    // Precondition: $\property{tree}(c)$
    using N = WeightType<decltype(c)>;
    if (empty(c)) return N{0};
    N l{0};
    N r{0};
    if (has_left_successor(c))
        l = height_recursive(left_successor(c));
    if (has_right_successor(c))
        r = height_recursive(right_successor(c));
    return successor(max(l, r));
}

enum visit { pre, in, post };

template<typename Proc>
auto traverse_nonempty(BifurcateCoordinate c, Proc proc) -> Proc
    requires Arity<Proc> == 2
    __requires(Procedure(Proc) && visit == InputType<Proc, 0> && decltype(C) == InputType<Proc, 1>)
{
    // Precondition: $\property{tree}(c) \wedge \neg \func{empty}(c)$
    proc(pre, c);
    if (has_left_successor(c))
        proc = traverse_nonempty(left_successor(c), proc);
    proc(in, c);
    if (has_right_successor(c))
        proc = traverse_nonempty(right_successor(c), proc);
    proc(post, c);
    return proc;
}

bool is_left_successor(BidirectionalBifurcateCoordinate j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    auto i = predecessor(j);
    return has_left_successor(i) && left_successor(i) == j;
}

bool is_right_successor(BidirectionalBifurcateCoordinate j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    auto i = predecessor(j);
    return has_right_successor(i) && right_successor(i) == j;
}

auto traverse_step(visit& v, BidirectionalBifurcateCoordinate& c)
{
    // Precondition: $\func{has\_predecessor}(c) \vee v \neq post$
    switch (v) {
    case pre:
        if (has_left_successor(c)) {
            c = left_successor(c);           return 1;
        }   v = in;                          return 0;
    case in:
        if (has_right_successor(c)) {
            v = pre; c = right_successor(c); return 1;
        }   v = post;                        return 0;
    case post:
        if (is_left_successor(c))
            v = in;
            c = predecessor(c);              return -1;
    }
}

template<BidirectionalBifurcateCoordinate C>
bool reachable(C x, C y)
{
    // Precondition: $\property{tree}(x)$
    if (empty(x)) return false;
    auto root = x;
    visit v = pre;
    do {
        if (x == y) return true;
        traverse_step(v, x);
    } while (x != root || v != post);
    return false;
}

auto weight(BidirectionalBifurcateCoordinate c)
{
    // Precondition: $\property{tree}(c)$
    using N = WeightType<decltype(c)>;
    if (empty(c)) return N{0};
    auto root = c;
    visit v = pre;
    N n{1}; // Invariant: $n$ is count of $\type{pre}$ visits so far
    do {
        traverse_step(v, c);
        if (v == pre) n = successor(n);
    } while (c != root || v != post);
    return n;
}

auto height(BidirectionalBifurcateCoordinate c)
{
    // Precondition: $\property{tree}(c)$
    using N = WeightType<decltype(c)>;
    if (empty(c)) return N{0};
    auto root = c;
    visit v = pre;
    N n{1}; // Invariant: $n$ is max of height of $\type{pre}$ visits so far
    N m{1}; // Invariant: $m$ is height of current $\type{pre}$ visit
    do {
        m = (m - N{1}) + N(traverse_step(v, c) + 1);
        n = max(n, m);
    } while (c != root || v != post);
    return n;
}

template<typename Proc>
auto traverse(BidirectionalBifurcateCoordinate c, Proc proc)
    requires Arity<Proc> == 2
    __requires(Procedure(Proc) && visit == InputType<Proc, 0> && decltype(c) == InputType<Proc, 1>)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    auto root = c;
    visit v = pre;
    proc(pre, c);
    do {
        traverse_step(v, c);
        proc(v, c);
    } while (c != root || v != post);
    return proc;
}


// Exercise 7.3: Use traverse_step and the procedures of Chapter 2 to determine
// whether the descendants of a bidirectional bifurcate coordinate form a DAG


template<BifurcateCoordinate C0, BifurcateCoordinate C1>
bool bifurcate_isomorphic_nonempty(C0 c0, C1 c1)
{
    // Precondition:
    // $\property{tree}(c0) \wedge \property{tree}(c1) \wedge \neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            if (!bifurcate_isomorphic_nonempty(left_successor(c0), left_successor(c1)))
                return false;
        } else return false;
    else if (has_left_successor(c1)) return false;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            if (!bifurcate_isomorphic_nonempty(right_successor(c0), right_successor(c1)))
                return false;
        } else return false;
    else if (has_right_successor(c1)) return false;
    return true;
}

template<BidirectionalBifurcateCoordinate C0, BidirectionalBifurcateCoordinate C1>
bool bifurcate_isomorphic(C0 c0, C1 c1)
{
    // Precondition: $\property{tree}(c0) \wedge \property{tree}(c1)$
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    auto root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<ReadableIterator I0, ReadableIterator I1>
bool lexicographical_equivalent(I0 f0, I0 l0, I1 f1, I1 l1, Relation r)
    __requires(ValueType<I0> == ValueType<I1> &&
        ValueType<I0> == Domain<decltype(r)>)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{equivalence}(r)$
    auto p = find_mismatch(f0, l0, f1, l1, r);
    return p.m0 == l0 && p.m1 == l1;
}

template<ReadableIterator I0, ReadableIterator I1>
bool lexicographical_equal(I0 f0, I0 l0, I1 f1, I1 l1)
    __requires(ValueType<I0> == ValueType<I1>)
{
    return lexicographical_equivalent(f0, l0, f1, l1, equal<ValueType<I0>>());
}

// Could specialize to use lexicographic_equal for k > some cutoff
template<int k, ReadableForwardIterator I0, ReadableForwardIterator I1>
    __requires(ValueType<I0> == ValueType<I1>)
struct lexicographical_equal_k
{
   bool operator()(I0 f0, I1 f1)
   {
       if (source(f0) != source(f1)) return false;
       return lexicographical_equal_k<k - 1, I0, I1>()(successor(f0), successor(f1));
   }
};

template<typename I0, typename I1>
struct lexicographical_equal_k<0, I0, I1>
{
    bool operator()(I0, I1)
    {
        return true;
    }
};

template<typename C>
concept bool ReadableBifurcateCoordinate = requires { Readable<C>() && BifurcateCoordinate<C>(); };

template<ReadableBifurcateCoordinate C0, ReadableBifurcateCoordinate C1>
bool bifurcate_equivalent_nonempty(C0 c0, C1 c1, Relation r)
    __requires(ValueType<C0> == ValueType<C1> && ValueType<C0> == Domain<R>)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if (!r(source(c0), source(c1))) return false;
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            if (!bifurcate_equivalent_nonempty(left_successor(c0), left_successor(c1), r))
                return false;
        } else return false;
    else if (has_left_successor(c1)) return false;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            if (!bifurcate_equivalent_nonempty(right_successor(c0), right_successor(c1), r))
                return false;
        } else return false;
    else if (has_right_successor(c1)) return false;
    return true;
}

template<typename C>
concept bool ReadableBidirectionalBifurcateCoordinate = requires { Readable<C>() && BidirectionalBifurcateCoordinate<C>(); };

template<ReadableBidirectionalBifurcateCoordinate C0, ReadableBidirectionalBifurcateCoordinate C1>
bool bifurcate_equivalent(C0 c0, C1 c1, Relation r)
    __requires(ValueType<C0> == ValueType<C1> && ValueType<C0> == Domain<decltype(r)>)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    auto root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        if (v0 == pre && !r(source(c0), source(c1))) return false;
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<ReadableBidirectionalBifurcateCoordinate C0, ReadableBidirectionalBifurcateCoordinate C1>
bool bifurcate_equal(C0 c0, C1 c1)
    __requires(ValueType<C0> == ValueType<C1>)
{
    return bifurcate_equivalent(c0, c1, equal<ValueType<C0>>());
}

template<ReadableIterator I0, ReadableIterator I1>
bool lexicographical_compare(I0 f0, I0 l0, I1 f1, I1 l1, Relation r)
    __requires(ValueType<I0> == ValueType<I1> && ValueType<I0> == Domain<R>)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{weak\_ordering}(r)$
    while (true) {
        if (f1 == l1) return false;
        if (f0 == l0) return true;
        if (r(source(f0), source(f1))) return true;
        if (r(source(f1), source(f0))) return false;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template<ReadableIterator I0, ReadableIterator I1>
bool lexicographical_less(I0 f0, I0 l0, I1 f1, I1 l1)
    __requires(ValueType<I0> == ValueType<I1>3)
{
    return lexicographical_compare(f0, l0, f1, l1, less<ValueType<I0>>());
}

template<int k, ReadableForwardIterator I0, ReadableForwardIterator I1>
    __requires(ValueType<I0> == ValueType<I1>)
struct lexicographical_less_k
{
   bool operator()(I0 f0, I1 f1)
   {
       if (source(f0) < source(f1)) return true;
       if (source(f0) > source(f1)) return false;
       return lexicographical_less_k<k - 1, I0, I1>()(successor(f0), successor(f1));
   }
};

template<typename I0, typename I1>
struct lexicographical_less_k<0, I0, I1>
{
    bool operator()(I0, I1)
    {
        return false;
    }
};


// Exercise 7.6: bifurcate_compare_nonempty (using 3-way comparsion)

// concept Comparator3Way(F) is
//     HomogeneousFunction(F)
//  /\ Arity<F> = 2
//  /\ Codomain<F> = int

// property(F : Comparator3Way)
// three_way_compare : F
//  f |- (all a,b in Domain<F>) f(a, b) in {-1, 0, 1}

//  Also need axioms equivalent to weak_order : transitivity, etc.
//  We could relax this to OrderedAdditiveGroup
//  (allowing subtraction as the comparator for numbers)
//  Should sense of positive/negative be flipped?

template<Relation R>
struct comparator_3_way
{
    using T = Domain<R>;
    R r;
    comparator_3_way(R r) : r{r}
    {
        // Precondition: $\property{weak\_ordering}(r)$
        // Postcondition: three_way_compare(comparator_3_way(r))
    }
    auto operator()(const T& a, const T& b)
    {
        if (r(a, b)) return 1;
        if (r(b, a)) return -1;
        return 0;
    }
};

template<ReadableIterator I0, ReadableIterator I1>
auto lexicographical_compare_3way(I0 f0, I0 l0, I1 f1, I1 l1, Comparator3Way comp)
    __requires(ValueType<I0> == ValueType<I1> && ValueType<I0> == Domain<decltype(comp)>)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    while (true) {
        if (f0 == l0)
            if (f1 == l1) return 0;
            else return 1;
        if (f1 == l1) return -1;
        auto tmp = comp(source(f0), source(f1));
        if (tmp != 0) return tmp;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template<ReadableBifurcateCoordinate C0, ReadableBifurcateCoordinate C1>
auto bifurcate_compare_nonempty(C0 c0, C1 c1, Comparator3Way comp)
    __requires(ValueType<C0> == ValueType<C1> && ValueType<I0> == Domain<decltype(comp)>)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    auto tmp = comp(source(c0), source(c1));
    if (tmp != 0) return tmp;
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            tmp = bifurcate_compare_nonempty(left_successor(c0), left_successor(c1), comp);
            if (tmp != 0) return tmp;
        } else return -1;
    else if (has_left_successor(c1)) return 1;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            tmp = bifurcate_compare_nonempty(right_successor(c0), right_successor(c1), comp);
            if (tmp != 0) return tmp;
        } else return -1;
    else if (has_right_successor(c1)) return 1;
    return 0;
}

template<ReadableBidirectionalBifurcateCoordinate C0, ReadableBidirectionalBifurcateCoordinate C1>
bool bifurcate_compare(C0 c0, C1 c1, Relation r)
    __requires(ValueType<C0> == ValueType<C1> && ValueType<C0> == Domain<decltype(r)>)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1) \wedge
    //                \property{weak\_ordering}(r)$
    if (empty(c1)) return false;
    if (empty(c0)) return true;
    auto root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        if (v0 == pre) {
            if (r(source(c0), source(c1))) return true;
            if (r(source(c1), source(c0))) return false;
        }
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return v0 > v1;
        if (c0 == root0 && v0 == post) return false;
    }
}

template<ReadableBidirectionalBifurcateCoordinate C0, ReadableBidirectionalBifurcateCoordinate C1>
bool bifurcate_less(C0 c0, C1 c1)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    return bifurcate_compare(c0, c1, less<ValueType<C0>>());
}

template<TotallyOrdered T>
struct always_false
{
    bool operator()(const T& x, const T& y)
    {
        return false;
    }
};

template<ReadableBidirectionalBifurcateCoordinate C0, ReadableBidirectionalBifurcateCoordinate C1>
bool bifurcate_shape_compare(C0 c0, C1 c1)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    return bifurcate_compare(c0, c1, always_false<ValueType<C0>>());
}


//
//  Chapter 8. Coordinates with mutable successors
//


// Models of ForwardLinker, BackwardLinker, and BidirectionalLinker
// assuming a particular representation of links

template<LinkedForwardIterator I>
struct forward_linker
{
    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
    }
};

template<LinkedForwardIterator I>
struct iterator_type<forward_linker<I>>
{
    using type = I;
};

template<LinkedBidirectionalIterator I>
struct backward_linker
{
    void operator()(I x, I y)
    {
        sink(y.p).backward_link = x.p;
    }
};

template<LinkedBidirectionalIterator I>
struct iterator_type<backward_linker<I>>
{
    using type = I;
};

template<LinkedBidirectionalIterator I>
struct bidirectional_linker
{
    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
        sink(y.p).backward_link = x.p;
    }
};

template<LinkedBidirectionalIterator I>
struct iterator_type<bidirectional_linker<I>>
{
    using type = I;
};

void advance_tail(ForwardIterator& t, ForwardIterator& f)
{
    // Precondition: $\func{successor}(f)\text{ is defined}$
    t = f;
    f = successor(f);
}

template<ForwardLinker S>
struct linker_to_tail
{
    using I = IteratorType<S>;
    S set_link;
    linker_to_tail(const S& set_link) : set_link{set_link} {}
    void operator()(I& t, I& f)
    {
        // Precondition: $\func{successor}(f)\text{ is defined}$
        set_link(t, f);
        advance_tail(t, f);
    }
};

auto find_last(ForwardIterator f, ForwardIterator l) -> ForwardIterator
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    decltype(f) t;
    do
        advance_tail(t, f);
    while (f != l);
    return t;
}

template<typename I, UnaryPseudoPredicate Pred>
auto split_linked(I f, I l, Pred p, ForwardLinker set_link)
    __requires(I == IteratorType<S> && I == Domain<Pred>)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    using P = pair<I, I>;
    linker_to_tail<decltype(set_link)> link_to_tail{set_link};
    I h0 = l; I t0 = l;
    I h1 = l; I t1 = l;
    if (f == l)                              goto s4;
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s0; }
s0: if (f == l)                              goto s4;
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s0; }
s1: if (f == l)                              goto s4;
    if (p(f)) {         advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s2; }
s2: if (f == l)                              goto s4;
    if (p(f)) {         link_to_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s2; }
s3: if (f == l)                              goto s4;
    if (p(f)) {         advance_tail(t1, f); goto s3; }
    else      {         link_to_tail(t0, f); goto s2; }
s4: return pair<P, P>{P(h0, t0), P(h1, t1)};
}

// Exercise 8.1: Explain the postcondition of split_linked


template<typename I>
auto combine_linked_nonempty(I f0, I l0, I f1, I l1, PseudoRelation r, ForwardLinker set_link)
    __requires(I == IteratorType<decltype(set_link)> && I == Domain<decltype(r)>)
{
    // Precondition: $\property{bounded\_range}(f0, l0) \wedge
    //                \property{bounded\_range}(f1, l1)$
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1 \wedge
    //                \property{disjoint}(f0, l0, f1, l1)$
    using T = triple<I, I, I>;
    linker_to_tail<decltype(set_link)> link_to_tail{set_link};
    I h; I t;
    if (r(f1, f0)) { h = f1; advance_tail(t, f1); goto s1; }
    else           { h = f0; advance_tail(t, f0); goto s0; }
s0: if (f0 == l0)                                 goto s2;
    if (r(f1, f0)) {         link_to_tail(t, f1); goto s1; }
    else           {         advance_tail(t, f0); goto s0; }
s1: if (f1 == l1)                                 goto s3;
    if (r(f1, f0)) {         advance_tail(t, f1); goto s1; }
    else           {         link_to_tail(t, f0); goto s0; }
s2: set_link(t, f1); return T{h, t, l1};
s3: set_link(t, f0); return T{h, t, l0};
}

// Exercise 8.2: combine_linked


template<typename I, ForwardLinker S>
    __requires(I == IteratorType<S>)
struct linker_to_head
{
    S set_link;
    linker_to_head(const S& set_link) : set_link{set_link} {}
    void operator()(I& h, I& f)
    {
        // Precondition: $\func{successor}(f)$ is defined
        auto tmp = successor(f);
        set_link(f, h);
        h = f;
        f = tmp;
    }
};

template<typename I>
auto reverse_append(I f, I l, I h, ForwardLinker set_link)
    __requires(I == IteratorType<decltype(set_link)>)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge h \notin [f, l)$
    linker_to_head<I, decltype(set_link)> link_to_head{set_link};
    while (f != l) link_to_head(h, f);
    return h;
}

template<Readable I, Predicate P>
    requires Same<ValueType<I>, Domain<P>>()
struct predicate_source
{
    P p;
    predicate_source(const P& p) : p{p} {}
    bool operator()(I i)
    {
        return p(source(i));
    }
};

template<typename I, ForwardLinker S, UnaryPredicate P>
    requires Same<I, IteratorType<S>>() && Same<ValueType<I>, Domain<P>>()
auto partition_linked(I f, I l, P p, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    predicate_source<I, P> ps(p);
    return split_linked(f, l, ps, set_link);
}

template<Readable I0, Readable I1, Relation R>
    requires Same<ValueType<I0>, ValueType<I1>>() && Same<ValueType<I0>, Domain<R>>()
struct relation_source
{
    R r;
    relation_source(const R& r) : r{r} {}
    bool operator()(I0 i0, I1 i1)
    {
        return r(source(i0), source(i1));
    }
};

template<Readable I>
auto merge_linked_nonempty(I f0, I l0, I f1, I l1, Relation r, ForwardLinker set_link)
    requires Same<I, IteratorType<decltype(set_link)>>()
        && Same<ValueType<I>, Domain<decltype(r)>>()
{
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1$
    // Precondition: $\property{increasing\_range}(f0, l0, r)$
    // Precondition: $\property{increasing\_range}(f1, l1, r)$
    relation_source<I, I, decltype(r)> rs{r};
    auto t = combine_linked_nonempty(f0, l0, f1, l1, rs, set_link);
    set_link(find_last(t.m1, t.m2), l1);
    return pair<I, I>{t.m0, l1};
}

template<Readable I, ForwardLinker S, Relation R>
    requires Same<I, IteratorType<S>>() && Same<ValueType<I>, Domain<R>>()
auto sort_linked_nonempty_n(I f, DistanceType<I> n, R r, S set_link)
{
    // Precondition: $\property{counted\_range}(f, n) \wedge
    //                n > 0 \wedge \func{weak\_ordering}(r)$
    using N = decltype(n);
    using P = pair<I, I>;
    if (n == N{1}) return P{f, successor(f)};
    auto h = half_nonnegative(n);
    auto p0 = sort_linked_nonempty_n(f, h, r, set_link);
    auto p1 = sort_linked_nonempty_n(p0.m1, n - h, r, set_link);
    return merge_linked_nonempty(p0.m0, p0.m1, p1.m0, p1.m1, r, set_link);
}

// Exercise 8.3: Complexity of sort_linked_nonempty_n


// Exercise 8.4: unique


void tree_rotate(EmptyLinkedBifurcateCoordinate& curr, EmptyLinkedBifurcateCoordinate& prev)
{
    // Precondition: $\neg \func{empty}(curr)$
    auto tmp = left_successor(curr);
    set_left_successor(curr, right_successor(curr));
    set_right_successor(curr, prev);
    if (empty(tmp)) { prev = tmp; return; }
    prev = curr;
    curr = tmp;
}

template<typename Proc>
auto traverse_rotating(EmptyLinkedBifurcateCoordinate c, Proc proc)
    requires Arity<Proc> == 1
    __requires(Procedure(Proc) && decltype(c) == InputType<Proc, 0>)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    auto curr = c;
    decltype(c) prev;
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    proc(curr);
    tree_rotate(curr, prev);
    return proc;
}

// Exercise 8.5: Diagram each state of traverse_rotating
// for a complete binary tree with 7 nodes


template<typename T, Integer N>
struct counter
{
    N n;
    counter() : n{0} {}
    counter(N n) : n{n} {}
    void operator()(const T&)
    {
        n = successor(n);
    }
};

auto weight_rotating(EmptyLinkedBifurcateCoordinate c)
{
    // Precondition: $\property{tree}(c)$
    using C = decltype(c);
    using N = WeightType<C>;
    return traverse_rotating(c, counter<C, N>{}).n / N{3};
}

template<Integer N, typename Proc>
    requires Arity<Proc> == 1
    __requires(Procedure(Proc))
struct phased_applicator
{
    N period;
    N phase;
    N n;
    // Invariant: $n, phase \in [0, period)$
    Proc proc;
    phased_applicator(N period, N phase, N n, Proc proc) :
        period{period}, phase{phase}, n{n}, proc{proc}
    {}
    void operator()(InputType<Proc, 0> x)
    {
        if (n == phase) proc(x);
        n = successor(n);
        if (n == period) n = 0;
    }
};

template<typename Proc>
Proc traverse_phased_rotating(EmptyLinkedBifurcateCoordinate c, int phase, Proc proc)
    requires Arity<Proc> == 1 && Same<decltype(c), InputType<Proc, 0>>()
    __requires(Procedure(Proc))
{
    // Precondition: $\property{tree}(c) \wedge 0 \leq phase < 3$
    phased_applicator<int, Proc> applicator{3, phase, 0, proc};
    return traverse_rotating(c, applicator).proc;
}


//
//  Chapter 9. Copying
//


template<typename O>
concept bool WritableIterator = requires { Writable<O>() && Iterator<O>(); };

void copy_step(ReadableIterator& f_i, WritableIterator& f_o)
    __requires(ValueType<decltype(i)> == ValueType<decltype(o)>)
{
    // Precondition: $\func{source}(f_i)$ and $\func{sink}(f_o)$ are defined
    sink(f_o) = source(f_i);
    f_i = successor(f_i);
    f_o = successor(f_o);
}

auto copy(ReadableIterator f_i, ReadableIterator l_i, WritableIterator f_o)
    __requires(ValueType<decltype(i)> == ValueType<decltype(o)>)
{
    // Precondition:
    // $\property{not\_overlapped\_forward}(f_i, l_i, f_o, f_o + (l_i - f_i))$
    while (f_i != l_i) copy_step(f_i, f_o);
    return f_o;
}

template<WritableIterator I>
void fill_step(I& f_o, const ValueType<I>& x)
{
    sink(f_o) = x;
    f_o = successor(f_o);
}

template<WritableIterator I>
I fill(I f, I l, const ValueType<I>& x)
{
    while (f != l) fill_step(f, x);
    return f;
}

template<WritableIterator O>
auto iota(ValueType<O> n, O o) // like APL $\iota$
    requires Integer<ValueType<O>>()
{
    // Precondition: $\property{writable\_counted\_range}(o, n) \wedge n \geq 0$
    return copy(ValueType<O>{0}, n, o);
}

// Useful for testing in conjunction with iota
template<ReadableIterator I>
bool equal_iota(I f, I l, ValueType<I> n = 0)
    requires Integer<ValueType<I>>()
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) != n) return false;
        n = successor(n);
        f = successor(f);
    }
    return true;
}

auto copy_bounded(ReadableIterator f_i, ReadableIterator l_i, WritableIterator f_o, WritableIterator l_o)
    __requires(ValueType<I> == ValueType<O>)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_o, l_o)$
    while (f_i != l_i && f_o != l_o) copy_step(f_i, f_o);
    return pair<decltype(f_i), decltype(f_o)>{f_i, f_o};
}

bool count_down(Integer& n)
{
    // Precondition: $n \geq 0$
    if (zero(n)) return false;
    n = predecessor(n);
    return true;
}

auto copy_n(ReadableIterator f_i, Integer n, WritableIterator f_o)
    __requires(ValueType<decltype(f_i)> == ValueType<decltype(f_o)>)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, f_i+n, f_o, f_o+n)$
    while (count_down(n)) copy_step(f_i, f_o);
    return pair<decltype(f_i), decltype(f_o)>{f_i, f_o};
}

template<WritableIterator I>
I fill_n(I f, DistanceType<I> n, const ValueType<I>& x)
{
    while (count_down(n)) fill_step(f, x);
    return f;
}

template<typename I>
concept bool WritableBidirectionalIterator = requires { Writable<I>() && BidirectionalIterator<I>(); };

void copy_backward_step(ReadableBidirectionalIterator& l_i, WritableBidirectionalIterator & l_o)
    __requires(ValueType<decltype(l_i)> == ValueType<decltype(l_o)>)
{
    // Precondition: $\func{source}(\property{predecessor}(l_i))$ and
    //               $\func{sink}(\property{predecessor}(l_o))$
    //               are defined
    l_i = predecessor(l_i);
    l_o = predecessor(l_o);
    sink(l_o) = source(l_i);
}

template<ReadableBidirectionalIterator I>
auto copy_backward(I f_i, I l_i, WritableBidirectionalIterator l_o)
    __requires(ValueType<I> == ValueType<decltype(l_o)>)
{
    // Precondition: $\property{not\_overlapped\_backward}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) copy_backward_step(l_i, l_o);
    return l_o;
}

template<ReadableBidirectionalIterator I>
auto copy_backward_n(I l_i, DistanceType<I> n, WritableBidirectionalIterator l_o)
    __requires(ValueType<I> == ValueType<decltype(l_o)>)
{
    while (count_down(n)) copy_backward_step(l_i, l_o);
    return pair<I, decltype(l_o)>{l_i, l_o};
}

void reverse_copy_step(ReadableBidirectionalIterator& l_i, WritableIterator& f_o)
    __requires(ValueType<decltype(l_i)> == ValueType<decltype(f_o)>)
{
    // Precondition: $\func{source}(\func{predecessor}(l_i))$ and
    //               $\func{sink}(f_o)$ are defined
    l_i = predecessor(l_i);
    sink(f_o) = source(l_i);
    f_o = successor(f_o);
}

void reverse_copy_backward_step(ReadableIterator& f_i, WritableBidirectionalIterator& l_o)
    __requires(ValueType<decltype(f_i)> == ValueType<decltype(l_o)>)
{
    // Precondition: $\func{source}(f_i)$ and
    //               $\func{sink}(\property{predecessor}(l_o))$ are defined
    l_o = predecessor(l_o);
    sink(l_o) = source(f_i);
    f_i = successor(f_i);
}

template<ReadableBidirectionalIterator I>
auto reverse_copy(I f_i, I l_i, WritableIterator f_o)
    __requires(ValueType<I> == ValueType<decltype(f_o)>)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, f_o, f_o+(l_i-f_i))$
    while (f_i != l_i) reverse_copy_step(l_i, f_o);
    return f_o;
}

template<ReadableIterator I>
auto reverse_copy_backward(I f_i, I l_i, WritableBidirectionalIterator l_o)
    __requires(ValueType<I> == ValueType<decltype(l_o)>)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) reverse_copy_backward_step(f_i, l_o);
    return l_o;
}

template<ReadableIterator I>
auto copy_select(I f_i, I l_i, WritableIterator f_t, UnaryPredicate p)
    __requires(ValueType<decltype(f_i)> == ValueType<decltype(f_t)>
        && I == Domain<decltype(p)>)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_t, f_t+n_t)$
    // where $n_t$ is an upper bound for the number of iterators satisfying $p$
    while (f_i != l_i)
        if (p(f_i)) copy_step(f_i, f_t);
        else f_i = successor(f_i);
    return f_t;
}

template<ReadableIterator I>
auto copy_if(I f_i, I l_i, WritableIterator f_t, UnaryPredicate p)
    __requires(ValueType<I> == ValueType<decltype(f_t)>
        && ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: same as for $\func{copy\_select}$
    predicate_source<I, decltype(p)> ps{p};
    return copy_select(f_i, l_i, f_t, ps);
}

template<ReadableIterator I, WritableIterator O_f, WritableIterator O_t>
auto split_copy(I f_i, I l_i, O_f f_f, O_t f_t, UnaryPredicate p)
    __requires(ValueType<I> == ValueType<O_f>
        && ValueType<I> == ValueType<O_t>
        && I == Domain<decltype(p)>)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i != l_i)
        if (p(f_i))
            copy_step(f_i, f_t);
        else
            copy_step(f_i, f_f);
    return pair<O_f, O_t>{f_f, f_t};
}

template<ReadableIterator I, WritableIterator O_f, WritableIterator O_t>
auto split_copy_n(I f_i, DistanceType<I> n_i, O_f f_f, O_t f_t, UnaryPredicate p)
    __requires(ValueType<I> == ValueType<O_f>
        && ValueType<I> == ValueType<O_t>
        && I == Domain<decltype(p)>)
{
    // Precondition: see exercise 9.2 of Elements of Programming
    while (count_down(n_i))
        if (p(f_i))
            copy_step(f_i, f_t);
        else
            copy_step(f_i, f_f);
    return pair<O_f, O_t>{f_f, f_t};
}

template<ReadableIterator I, WritableIterator O_f, WritableIterator O_t>
auto partition_copy(I f_i, I l_i, O_f f_f, O_t f_t, UnaryPredicate p)
    __requires(ValueType<I> == ValueType<O_f>
        && ValueType<I> == ValueType<O_t>
        && ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: same as $\func{split\_copy}$
    predicate_source<I, decltype(p)> ps{p};
    return split_copy(f_i, l_i, f_f, f_t, ps);
}

template<ReadableIterator I, WritableIterator O_f, WritableIterator O_t>
auto partition_copy_n(I f_i, DistanceType<I> n, O_f f_f, O_t f_t, auto p)
    __requires(ValueType<I> == ValueType<O_f> &&
        ValueType<I> == ValueType<O_t> &&
        UnaryPredicate(decltype(p)) && ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: see $\func{partition_copy}$
    predicate_source<I, decltype(p)> ps{p};
    return split_copy_n(f_i, n, f_f, f_t, ps);
}

template<ReadableIterator I0, ReadableIterator I1, WritableIterator O>
auto combine_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, BinaryPredicate r)
    __requires(ValueType<I0> == ValueType<O>
        && ValueType<I1> == ValueType<O>
        && I0 == InputType<decltype(r), 1> && I1 == InputType<decltype(r), 0>)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1)
        if (r(f_i1, f_i0))
            copy_step(f_i1, f_o);
        else
            copy_step(f_i0, f_o);
    return copy(f_i1, l_i1, copy(f_i0, l_i0, f_o));
}

template<ReadableIterator I0, ReadableIterator I1>
auto combine_copy_n(
    I0 f_i0, DistanceType<I0> n_i0,
    I1 f_i1, DistanceType<I1> n_i1,
    WritableIterator f_o, BinaryPredicate r
)
    __requires(ValueType<I0> == ValueType<decltype(f_o)>
        && ValueType<I1> == ValueType<decltype(f_o)>
        && I0 == InputType<R, 1> && I1 = InputType<R, 0>)
{
    // Precondition: see $\func{combine_copy}$
    using Triple = triple<I0, I1, decltype(f_o)>;
    while (true) {
        if (zero(n_i0)) {
            auto p = copy_n(f_i1, n_i1, f_o);
            return Triple(f_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            auto p = copy_n(f_i0, n_i0, f_o);
            return Triple(p.m0, f_i1, p.m1);
        }
        if (r(f_i1, f_i0)) {
            copy_step(f_i1, f_o);
            n_i1 = predecessor(n_i1);
        } else             {
            copy_step(f_i0, f_o);
            n_i0 = predecessor(n_i0);
        }
    }
}

template<ReadableBidirectionalIterator I0, ReadableBidirectionalIterator I1>
auto combine_copy_backward(
    I0 f_i0, I0 l_i0,
    I1 f_i1, I1 l_i1,
    WritableBidirectionalIterator l_o, BinaryPredicate r
)
    __requires(ValueType<I0> == ValueType<decltype(l_o)>
        && ValueType<I1> == ValueType<decltype(l_o)>
        && I0 == InputType<decltype(r), 1> && I1 == InputType<decltype(r), 0>)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1) {
        if (r(predecessor(l_i1), predecessor(l_i0)))
            copy_backward_step(l_i0, l_o);
        else
            copy_backward_step(l_i1, l_o);
    }
    return copy_backward(f_i0, l_i0, copy_backward(f_i1, l_i1, l_o));
}

template<ReadableBidirectionalIterator I0, ReadableBidirectionalIterator I1>
auto combine_copy_backward_n(
    I0 l_i0, DistanceType<I0> n_i0,
    I1 l_i1, DistanceType<I1> n_i1,
    WritableBidirectionalIterator l_o, BinaryPredicate r
)
    __requires(ValueType<I0> == ValueType<decltype(l_o)>
        && ValueType<I1> == ValueType<decltype(l_o)>
        && I0 == InputType<decltype(r), 1> && I1 = InputType<decltype(r), 0>)
{
    // Precondition: see $\func{combine\_copy\_backward}$
    using Triple = triple<I0, I1, decltype(l_o)>;
    while (true) {
        if (zero(n_i0)) {
            auto p = copy_backward_n(l_i1, n_i1, l_o);
            return Triple(l_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            auto p = copy_backward_n(l_i0, n_i0, l_o);
            return Triple(p.m0, l_i1, p.m1);
        }
        if (r(predecessor(l_i1), predecessor(l_i0))) {
            copy_backward_step(l_i0, l_o);
            n_i0 = predecessor(n_i0);
        } else {
            copy_backward_step(l_i1, l_o);
            n_i1 = predecessor(n_i1);
        }
    }
}

template<ReadableIterator I0, ReadableIterator I1>
auto merge_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, WritableIterator f_o, Relation r)
    __requires(ValueType<I0> == ValueType<decltype(f_o)>
        && ValueType<I1> == ValueType<decltype(f_o)>
        && ValueType<I0> == Domain<decltype(r)>)
{
    // Precondition: in addition to that for $\func{combine\_copy}$:
    // \hspace*{1em} $\property{weak\_ordering}(r) \wedge {}$
    // \hspace*{1em} $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, decltype(r)> rs{r};
    return combine_copy(f_i0, l_i0, f_i1, l_i1, f_o, rs);
}

template<ReadableIterator I0, ReadableIterator I1>
auto merge_copy_n(
    I0 f_i0, DistanceType<I0> n_i0,
    I1 f_i1, DistanceType<I1> n_i1,
    WritableIterator o, Relation r
)
    __requires(ValueType<I0> == ValueType<O>
        && ValueType<I1> == ValueType<decltype(o)>
        && ValueType<I0> == Domain<decltype(r)>)
{
    // Precondition: see $\func{merge\_copy}$
    relation_source<I1, I0, decltype(r)> rs{r};
    return combine_copy_n(f_i0, n_i0, f_i1, n_i1, o, rs);
}

template<ReadableBidirectionalIterator I0, ReadableBidirectionalIterator I1>
auto merge_copy_backward(
    I0 f_i0, I0 l_i0,
    I1 f_i1, I1 l_i1,
    WritableBidirectionalIterator l_o, Relation r
)
    __requires(ValueType<I0> == ValueType<decltype(l_o)>
        && ValueType<I1> == ValueType<decltype(l_o)>
        && ValueType<I0> == Domain<decltype(r)>)
{
    // Precondition: in addition to that for $\func{combine\_copy\_backward}$:
    //               $\property{weak\_ordering}(r) \wedge {}$
    //               $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, decltype(r)> rs{r};
    return combine_copy_backward(f_i0, l_i0, f_i1, l_i1, l_o, rs);
}

template<ReadableBidirectionalIterator I0, ReadableBidirectionalIterator I1>
auto merge_copy_backward_n(
    I0 l_i0, DistanceType<I0> n_i0,
    I1 l_i1, DistanceType<I1> n_i1,
    WritableBidirectionalIterator l_o, Relation r
)
    __requires(ValueType<I0> == ValueType<O>
        && ValueType<I1> == ValueType<O>
        && ValueType<I0> == Domain<R>)
{
    // Precondition: see $\func{merge\_copy\_backward}$
    relation_source<I1, I0, decltype(r)> rs{r};
    return combine_copy_backward_n(l_i0, n_i0, l_i1, n_i1, l_o, rs);
}

template<Mutable I0, Mutable I1>
void exchange_values(I0 x, I1 y)
    __requires(ValueType<I0> == ValueType<I1>)
{
    // Precondition: $\func{deref}(x)$ and $\func{deref}(y)$ are defined
    ValueType<I0> t = source(x);
    sink(x) = source(y);
    sink(y) = t;
}

template<typename I>
concept bool MutableForwardIterator = requires { Mutable<I>() && ForwardIterator<I>(); };

template<MutableForwardIterator I0, MutableForwardIterator I1>
void swap_step(I0& f0, I1& f1)
    __requires(ValueType<I0> == ValueType<I1>)
{
    // Precondition: $\func{deref}(f_0)$ and $\func{deref}(f_1)$ are defined
    exchange_values(f0, f1);
    f0 = successor(f0);
    f1 = successor(f1);
}

template<MutableForwardIterator I0, MutableForwardIterator I1>
auto swap_ranges(I0 f0, I0 l0, I1 f1)
    __requires(ValueType<I0> == ValueType<I1>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) swap_step(f0, f1);
    return f1;
}

template<MutableForwardIterator I0, MutableForwardIterator I1>
auto swap_ranges_bounded(I0 f0, I0 l0, I1 f1, I1 l1)
    __requires(ValueType<I0> == ValueType<I1>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1) swap_step(f0, f1);
    return pair<I0, I1>{f0, f1};
}

template<MutableForwardIterator I0, MutableForwardIterator I1>
auto swap_ranges_n(I0 f0, I1 f1, Integer n)
    __requires(ValueType<I0> == ValueType<I1>)
{
    // Precondition: $\property{mutable\_counted\_range}(f_0, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) swap_step(f0, f1);
    return pair<I0, I1>{f0, f1};
}

template<typename I>
concept bool MutableBidirectionalIterator = requires { Mutable<I>() && BidirectionalIterator<I>(); };

void reverse_swap_step(MutableBidirectionalIterator& l0, MutableForwardIterator& f1)
    __requires(ValueType<decltype(l0)> == ValueType<decltype(f1)>)
{
    // Precondition: $\func{deref}(\func{predecessor}(l_0))$ and
    //               $\func{deref}(f_1)$ are defined
    l0 = predecessor(l0);
    exchange_values(l0, f1);
    f1 = successor(f1);
}

auto reverse_swap_ranges(
    MutableBidirectionalIterator f0, MutableBidirectionalIterator l0,
    MutableForwardIterator f1
)
    __requires(ValueType<decltype(f0)> == ValueType<decltype(f1)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) reverse_swap_step(l0, f1);
    return f1;
}

auto reverse_swap_ranges_bounded(
    MutableBidirectionalIterator f0, MutableBidirectionalIterator l0,
    MutableForwardIterator f1, MutableForwardIterator l1
)
    __requires(ValueType<decltype(f0)> == ValueType<decltype(f1)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition:  $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1)
        reverse_swap_step(l0, f1);
    return pair<decltype(l0), decltype(f1)>{l0, f1};
}

auto reverse_swap_ranges_n(
    MutableBidirectionalIterator l0, MutableForwardIterator f1, Integer n
)
    __requires(ValueType<decltype(l0)> == ValueType<decltype(f1)>)
{
    // Precondition: $\property{mutable\_counted\_range}(l_0-n, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) reverse_swap_step(l0, f1);
    return pair<decltype(l0), decltype(f1)>{l0, f1};
}


//
//  Chapter 10. Rearrangements
//


void cycle_to(Mutable i, Transformation f)
    __requires(decltype(i) == Domain<decltype(f)>)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    auto k = f(i);
    while (k != i) {
        exchange_values(i, k);
        k = f(k);
    }
}

// Exercise 10.3: cycle_to variant doing 2n-1 assignments


void cycle_from(Mutable i, Transformation f)
    __requires(decltype(i) == Domain<decltype(f)>)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    auto tmp = source(i);
    auto j = i;
    auto k = f(i);
    while (k != i) {
        sink(j) = source(k);
        j = k;
        k = f(k);
    }
    sink(j) = tmp;
}


// Exercise 10.4: arbitrary rearrangement using array of n boolean values
// Exercise 10.5: arbitrary rearrangement using total ordering on iterators


template<typename I>
void reverse_n_indexed(I f, DistanceType<I> n)
    requires Mutable<I>() && IndexedIterator<I>()
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    decltype(n) i{0};
    n = predecessor(n);
    while (i < n) {
        // $n = (n_\text{original} - 1) - i$
        exchange_values(f + i, f + n);
        i = successor(i);
        n = predecessor(n);
    }
}

template<typename I>
concept bool MutableBidirectionalIterator = requires { Mutable<I>() && BidirectionalIterator<I>(); };

void reverse_bidirectional(
    MutableBidirectionalIterator f, MutableBidirectionalIterator l
)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        if (f == l) return;
        l = predecessor(l);
        if (f == l) return;
        exchange_values(f, l);
        f = successor(f);
    }
}

template<MutableBidirectionalIterator I>
void reverse_n_bidirectional(I f, I l, DistanceType<I> n)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge 0 \leq n \leq l - f$
    reverse_swap_ranges_n(l, f, half_nonnegative(n));
}

template<typename I>
concept bool MutableForwardIterator = requires { Mutable<I>() && ForwardIterator<I>(); };

template<MutableForwardIterator I>
auto reverse_n_with_buffer(I f_i, DistanceType<I> n, MutableBidirectionalIterator f_b)
    __requires(ValueType<I> == ValueType<B>)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n)$
    return reverse_copy(f_b, copy_n(f_i, n, f_b).m1, f_i);
}

template<MutableForwardIterator I>
auto reverse_n_forward(I f, DistanceType<I> n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    using N = DistanceType<I>;
    if (n < N(2)) return f + n;
    N h = half_nonnegative(n);
    N n_mod_2 = n - twice(h);
    I m = reverse_n_forward(f, h) + n_mod_2;
    I l = reverse_n_forward(m, h);
    swap_ranges_n(f, m, h);
    return l;
}

template<MutableForwardIterator I>
auto reverse_n_adaptive(
    I f_i, DistanceType<I> n_i, MutableBidirectionalIterator f_b, DistanceType<I> n_b
)
        __requires(ValueType<I> == ValueType<B>)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n_i)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    using N = DistanceType<I>;
    if (n_i < N(2))
        return f_i + n_i;
    if (n_i <= n_b)
        return reverse_n_with_buffer(f_i, n_i, f_b);
    N h_i = half_nonnegative(n_i);
    N n_mod_2 = n_i - twice(h_i);
    I m_i = reverse_n_adaptive(f_i, h_i, f_b, n_b) + n_mod_2;
    I l_i = reverse_n_adaptive(m_i, h_i, f_b, n_b);
    swap_ranges_n(f_i, m_i, h_i);
    return l_i;
}

template<RandomAccessIterator I>
struct k_rotate_from_permutation_random_access
{
    DistanceType<I> k;
    DistanceType<I> n_minus_k;
    I m_prime;
    k_rotate_from_permutation_random_access(I f, I m, I l)
        : k{l - m}, n_minus_k{m - f}, m_prime{f + (l - m)}
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        if (x < m_prime) return x + n_minus_k;
        return x - k;
    }
};

template<IndexedIterator I>
struct k_rotate_from_permutation_indexed
{
    DistanceType<I> k;
    DistanceType<I> n_minus_k;
    I f;
    k_rotate_from_permutation_indexed(I f, I m, I l)
        : k{l - m}, n_minus_k{m - f}, f{f}
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        DistanceType<I> i = x - f;
        if (i < k) return x + n_minus_k;
        return f + (i - k);
    }
};

template<typename I>
concept bool MutableIndexedIterator = requires { Mutable<I>() && IndexedIterator<I>(); };

template<MutableIndexedIterator I>
auto rotate_cycles(I f, I m, I l, Transformation from)
    __requires(I == Domain<decltype(from)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    // Precondition: $from$ is a from-permutation on $[f, l)$
    using N = DistanceType<I>;
    N d = gcd<N, N>(m - f, l - m);
    while (count_down(d)) cycle_from(f + d, from);
    return f + (l - m);
}

template<MutableIndexedIterator I>
auto rotate_indexed_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_indexed<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}

template<typename I>
concept bool MutableRandomAccessIterator = requires { Mutable<I>() && RandomAccessIterator<I>(); };

template<MutableRandomAccessIterator I>
auto rotate_random_access_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_random_access<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}


template<MutableBidirectionalIterator I>
auto rotate_bidirectional_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    reverse_bidirectional(f, m);
    reverse_bidirectional(m, l);
    auto p = reverse_swap_ranges_bounded(m, l, f, m);
    reverse_bidirectional(p.m1, p.m0);
    if (m == p.m0) return p.m1;
    return p.m0;
}

template<MutableForwardIterator I>
void rotate_forward_annotated(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    auto a = m - f;
    auto b = l - m;
    while (true) {
        auto p = swap_ranges_bounded(f, m, m, l);
        if (p.m0 == m && p.m1 == l) { Assert(a == b);
            return;
        }
        f = p.m0;
        if (f == m) {                 Assert(b > a);
            m = p.m1;                 b = b - a;
        } else {                      Assert(a > b);
                                      a = a - b;
        }
    }
}

template<MutableForwardIterator I>
void rotate_forward_step(I& f, I& m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    auto c = m;
    do {
        swap_step(f, c);
        if (f == m) m = c;
    } while (c != l);
}

template<MutableForwardIterator I>
auto rotate_forward_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    rotate_forward_step(f, m, l);
    auto m_prime = f;
    while (m != l) rotate_forward_step(f, m, l);
    return m_prime;
}

template<MutableForwardIterator I>
auto rotate_partial_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return swap_ranges(m, l, f);
}

// swap_ranges_backward
// rotate_partial_backward_nontrivial

template<MutableForwardIterator I, MutableForwardIterator B>
auto rotate_with_buffer_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    auto l_b = copy(f, m, f_b);
    auto m_prime = copy(m, l, f);
    copy(f_b, l_b, m_prime);
    return m_prime;
}

template<MutableBidirectionalIterator I, MutableForwardIterator B>
auto rotate_with_buffer_backward_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    auto l_b = copy(m, l, f_b);
    copy_backward(f, m, l);
    return copy(f_b, l_b, f);
}


// Section 10.5. Algorithm selection


void reverse_indexed(MutableIndexedIterator f, MutableIndexedIterator l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    reverse_n_indexed(f, l - f);
}


// temporary_buffer type

template<typename I>
concept bool WritableForwardIterator = requires { Writable<I>() && ForwardIterator<I>(); };

void construct_all(WritableForwardIterator f, WritableForwardIterator l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a default-constructed state}$
    // We assume if an iterator is writable, its value can be constructed
    construct_all(f, l, NeedsConstruction<ValueType<decltype(f)>>());
}

void construct_all(WritableForwardIterator f, WritableForwardIterator l, true_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // We assume if an iterator is writable, its value can be constructed
    while (f != l) {
        construct(sink(f));
        f = successor(f);
    }
}

void construct_all(WritableForwardIterator /*f*/, WritableForwardIterator /*l*/, false_type)
    __requires(NeedsConstruction<ValueType<I>> == false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}

void destroy_all(WritableForwardIterator f, WritableForwardIterator l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writable, its value can be destroyed
    destroy_all(f, l, NeedsDestruction<ValueType<decltype(f)>>());
}

void destroy_all(WritableForwardIterator f, WritableForwardIterator l, true_type)
{
    // Precondition: $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition: $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writable, its value can be destroyed
    while (f != l) {
        destroy(sink(f));
        f = successor(f);
    }
}

void destroy_all(WritableForwardIterator /*f*/, WritableForwardIterator /*l*/, false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}

// NeedsConstruction and NeedsDestruction should be overloaded for every POD type

template<Regular T>
struct temporary_buffer
{
    using P = pointer(T);
    using N = DistanceType<P>;
    P p;
    N n;
    temporary_buffer(N n_) : n{n_}
    {
        while (true) {
            p = P(malloc(n * sizeof(T)));
            if (p != P(0)) {
                construct_all(p, p + n);
                return;
            }
            n = half_nonnegative(n);
        }
    }
    ~temporary_buffer()
    {
        destroy_all(p, p + n);
        free(p);
    }
    temporary_buffer(const temporary_buffer&) = delete;
    void operator=(const temporary_buffer&) = delete;
};

auto size(const temporary_buffer<Regular>& b)
{
    return b.n;
}

auto begin(temporary_buffer<Regular>& b)
{
    return b.p;
}

template<MutableForwardIterator I>
void reverse_n_with_temporary_buffer(I f, DistanceType<I> n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    temporary_buffer<ValueType<I>> b(n);
    reverse_n_adaptive(f, n, begin(b), size(b));
}

template<MutableForwardIterator I>
auto rotate(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    if (m == f) return l;
    if (m == l) return f;
    return rotate_nontrivial(f, m, l, IteratorConcept(I){});
}

template<MutableForwardIterator I>
auto rotate_nontrivial(I f, I m, I l, forward_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_forward_nontrivial(f, m, l);
}

template<MutableBidirectionalIterator I>
auto rotate_nontrivial(I f, I m, I l, bidirectional_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_bidirectional_nontrivial(f, m, l);
}

template<MutableIndexedIterator I>
auto rotate_nontrivial(I f, I m, I l, indexed_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_indexed_nontrivial(f, m, l);
}

template<MutableRandomAccessIterator I>
auto rotate_nontrivial(I f, I m, I l, random_access_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_random_access_nontrivial(f, m, l);
}


//
//  Chapter 11. Partition and merging
//


// Exercise 11.1:

bool partitioned_at_point(
    ReadableIterator f, ReadableIterator m, ReadableIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    return none(f, m, p) && all(m, l, p);
}


// Exercise 11.2:

auto potential_partition_point(
    ReadableForwardIterator f, ReadableForwardIterator l,
    UnaryPredicate p
)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    return count_if_not(f, l, p, f);
}

auto partition_semistable(
    MutableForwardIterator f, MutableForwardIterator l,
    UnaryPredicate p
)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    auto i = find_if(f, l, p);
    if (i == l) return i;
    auto j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        swap_step(i, j);
    }
}

// Exercise 11.3: rewrite partition_semistable, expanding find_if_not inline and
// eliminating extra test against l


// Exercise 11.4: substitute copy_step(j, i) for swap_step(i, j) in partition_semistable

auto remove_if(
    MutableForwardIterator f, MutableForwardIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    auto i = find_if(f, l, p);
    if (i == l) return i;
    auto j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        copy_step(j, i);
    }
}


// Exercise 11.5:

//template<typename I, typename P>
//    __requires(Mutable(I) && ForwardIterator(I) &&
//        UnaryPredicate(P) && ValueType<I> == Domain<P>)
//void partition_semistable_omit_last_predicate_evaluation(I f, I l, P p)
//{
//    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
//    ...
//}

auto partition_bidirectional(
    MutableBidirectionalIterator f, MutableBidirectionalIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        f = find_if(f, l, p);
        l = find_backward_if_not(f, l, p);
        if (f == l) return f;
        reverse_swap_step(l, f);
    }
}

// Exercise 11.6:

auto partition_forward(
    MutableForwardIterator f, MutableForwardIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    auto i = count_if_not(f, l, p, f);
    auto j = i;
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        f = find_if_unguarded(f, p);
        swap_step(f, j);
    }
}

// Exercise 11.7: partition_single_cycle

auto partition_single_cycle(
    MutableBidirectionalIterator f, MutableBidirectionalIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    auto tmp = source(f);
    while (true) {
        sink(f) = source(l);
        f = find_if(successor(f), l, p);
        if (f == l) {
            sink(l) = tmp;
            return f;
        }
        sink(l) = source(f);
        l = find_backward_if_not_unguarded(l, p);
    }
}


// Exercise 11.8: partition_sentinel

auto partition_bidirectional_unguarded(
    MutableBidirectionalIterator f, MutableBidirectionalIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(p)> == Domain<decltype(p)>)
{
    // Precondition:
    // $(\neg \func{all}(f, l, p) \wedge \func{some}(f, l, p)) \vee
    // (\neg p(\func{source}(f-1)) \wedge p(\func{source}(l)))$
    while (true) {
        f = find_if_unguarded(f, p);
        l = find_backward_if_not_unguarded(l, p);
        if (successor(l) == f) return f;
        exchange_values(f, l);
        f = successor(f); // $\neg p(\func{source}(f-1)) \wedge p(\func{source}(l))$
    }
}

auto partition_sentinel(
    MutableBidirectionalIterator f, MutableBidirectionalIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    exchange_values(f, l);
    f = successor(f);
    return partition_bidirectional_unguarded(f, l, p);
}


// Exercise 11.9: partition_single_cycle_sentinel


auto partition_indexed(
    MutableIndexedIterator f, MutableIndexedIterator l,
    UnaryPredicate p
)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    using N = DistanceType<decltype(f)>;
    N i{0};
    auto j = l - f;
    while (true) {
        while (true) {
            if (i == j) return f + i;
            if (p(source(f + i))) break;
            i = successor(i);
        }
        while (true) {
            j = predecessor(j);
            if (i == j) return f + j + 1;
            if (!p(source(f + j))) break;
        }
        exchange_values(f + i, f + j);
        i = successor(i);
    }
}

template<MutableForwardIterator I, MutableForwardIterator B>
auto partition_stable_with_buffer(I f, I l, B f_b, UnaryPredicate p)
    __requires(ValueType<I> == ValueType<B> &&
        ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    auto x = partition_copy(f, l, f, f_b, p);
    copy(f_b, x.m1, x.m0);
    return x.m0;
}

auto partition_stable_singleton(MutableForwardIterator f, UnaryPredicate p)
    __requires(ValueType<decltype(f)> == Domain<decltype(p)>)
{
    // Precondition: $\property{readable\_bounded\_range}(f, \func{successor}(f))$
    auto l = successor(f);
    if (!p(source(f))) f = l;
    return pair<decltype(f), decltype(l)>{f, l};
}

template<MutableForwardIterator I>
auto combine_ranges(const pair<I, I>& x, const pair<I, I>& y)
{
    // Precondition: $\property{mutable\_bounded\_range}(x.m0, y.m0)$
    // Precondition: $x.m1 \in [x.m0, y.m0]$
    return pair<I, I>{rotate(x.m0, x.m1, y.m0), y.m1};
}

template<MutableForwardIterator I>
auto partition_stable_n_nonempty(I f, DistanceType<I> n, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge n > 0$
    if (one(n)) return partition_stable_singleton(f, p);
    auto h = half_nonnegative(n);
    auto x = partition_stable_n_nonempty(f, h, p);
    auto y = partition_stable_n_nonempty(x.m1, n - h, p);
    return combine_ranges(x, y);
}

template<MutableForwardIterator I>
auto partition_stable_n(I f, DistanceType<I> n, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    if (zero(n)) return pair<I, I>{f, f};
    return partition_stable_n_nonempty(f, n, p);
}


// Exercise 11.10: partition_stable_n_adaptive


template<MutableForwardIterator I>
auto partition_stable(I f, I l, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    return partition_stable_n(f, l - f, p).m0;
}

template<ForwardIterator I, UnaryPredicate P>
    __requires(ValueType<I> == Domain<P>)
struct partition_trivial
{
    P p;
    partition_trivial(const P& p) : p{p} {}
    auto operator()(I i) -> pair<I, I>
    {
        return partition_stable_singleton<I, P>(i, p);
    }
};

template<ForwardIterator I, UnaryPredicate P>
    __requires(ValueType<I> == Domain<P>)
struct codomain_type< partition_trivial<I, P>>
{
    using type = pair<I, I>;
};

template<MutableForwardIterator I, BinaryOperation Op>
Domain<Op> add_to_counter(I f, I l, Op op, Domain<Op> x, const Domain<Op>& z)
    __requires(ValueType<I> == Domain<Op>)
{
    if (x == z) return z;
    while (f != l) {
        if (source(f) == z) {
            sink(f) = x;
            return z;
        }
        x = op(source(f), x);
        sink(f) = z;
        f = successor(f);
    }
    return x;
}

template<BinaryOperation Op>
struct counter_machine
{
    using T = Domain<Op>;
    Op op;
    T z;
    T f[64];
    pointer(T) l;
    counter_machine(Op op, const Domain<Op>& z) : op{op}, z{z}, l{f} {}
    void operator()(const T& x)
    {
        // Precondition: must not be called more than $2^{64}-1$ times
        auto tmp = add_to_counter(f, l, op, x, z);
        if (tmp != z) {
            sink(l) = tmp;
            l = successor(l);
        }
    }
};

template<BinaryOperation Op>
struct transpose_operation
{
    Op op;
    transpose_operation(Op op) : op{op} {}
    using T = Domain<Op>;
    T operator()(const T& x, const T& y)
    {
        return op(y, x);
    }
};

template<BinaryOperation Op>
struct input_type<transpose_operation<Op>, 0>
{
    using type = Domain<Op>;
};

template<Iterator I, BinaryOperation Op, UnaryFunction F>
Domain<Op> reduce_balanced(I f, I l, Op op, F fun, const Domain<Op>& z)
    __requires(I == Domain<F> && Codomain<F> == Domain<Op>)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    counter_machine<Op> c{op, z};
    while (f != l) {
        c(fun(f));
        f = successor(f);
    }
    transpose_operation<Op> t_op{op};
    return reduce_nonzeroes(c.f, c.l, t_op, z);
}

template<BinaryOperation Op>
auto reduce_balanced(Iterator f, Iterator l, Op op, const Domain<Op>& z)
    __requires(ValueType<I> == Domain<Op>)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge l-f < 2^{33}$
    // Precondition: $\property{partially\_associative}(op)$
    counter_machine<Op> c{op, z};
    while (f != l) {
        c(source(f));
        f = successor(f);
    }
    transpose_operation<Op> t_op{op};
    return reduce_nonzeroes(c.f, c.l, t_op, z);
}


template<UnaryPredicate P>
auto partition_stable_iterative(ForwardIterator f, ForwardIterator l, P p)
    __requires(ValueType<I> == Domain<P>)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    using I = decltype(f);
    return reduce_balanced(
        f, l,
        combine_ranges<I>,
        partition_trivial<I, P>(p),
        pair<I, I>(f, f)
      ).m0;
}

template<MutableForwardIterator I, MutableForwardIterator B>
auto merge_n_with_buffer(
    I f0, DistanceType<I> n0,
    I f1, DistanceType<I> n1,
    B f_b, Relation r
)
    __requires(ValueType<I> == ValueType<B> && ValueType<I> == Domain<decltype(r)>)
{
    // Precondition: $\func{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_0)$
    copy_n(f0, n0, f_b);
    return merge_copy_n(f_b, n0, f1, n1, f0, r).m2;
}

template<MutableForwardIterator I, MutableForwardIterator B>
auto sort_n_with_buffer(I f, DistanceType<I> n, B f_b, Relation r)
    __requires(ValueType<I> == ValueType<B> && ValueType<I> == Domain<decltype(r)>)
{
    // Property:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, \lceil n/2 \rceil)$
    auto h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_with_buffer(f, h, f_b, r);
    sort_n_with_buffer(m, n - h, f_b, r);
    return merge_n_with_buffer(f, h, m, n - h, f_b, r);
}

template<MutableForwardIterator I>
void merge_n_step_0(
    I f0, DistanceType<I> n0,
    I f1, DistanceType<I> n1, Relation r,
    I& f0_0, DistanceType<I>& n0_0,
    I& f0_1, DistanceType<I>& n0_1,
    I& f1_0, DistanceType<I>& n1_0,
    I& f1_1, DistanceType<I>& n1_1
)
    __requires(ValueType<I> == Domain<decltype(r)>)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_0 = half_nonnegative(n0);
    f0_1 = f0_0 + n0_0;
    f1_1 = lower_bound_n(f1, n1, source(f0_1), r);
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_1 = f1_0 - f0_1;
    f1_0 = successor(f1_0);
    n1_0 = predecessor(n0 - n0_0);
    n1_1 = n1 - n0_1;
}

template<MutableForwardIterator I>
void merge_n_step_1(
    I f0, DistanceType<I> n0,
    I f1, DistanceType<I> n1, Relation r,
    I& f0_0, DistanceType<I>& n0_0,
    I& f0_1, DistanceType<I>& n0_1,
    I& f1_0, DistanceType<I>& n1_0,
    I& f1_1, DistanceType<I>& n1_1
)
    __requires(ValueType<I> == Domain<decltype(r)>)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_1 = half_nonnegative(n1);
    f1_1 = f1 + n0_1;
    f0_1 = upper_bound_n(f0, n0, source(f1_1), r);
    f1_1 = successor(f1_1);
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_0 = f0_1 - f0_0;
    n1_0 = n0 - n0_0;
    n1_1 = predecessor(n1 - n0_1);
}

template<MutableForwardIterator I, MutableForwardIterator B>
auto merge_n_adaptive(
    I f0, DistanceType<I> n0,
    I f1, DistanceType<I> n1,
    B f_b, DistanceType<B> n_b, Relation r
)
    requires Same<ValueType<I>, ValueType<B>>()
    __requires(ValueType<I> == Domain<decltype(r)>)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    using N = DistanceType<I>;
    if (zero(n0) || zero(n1)) return f0 + n0 + n1;
    if (n0 <= N(n_b))
        return merge_n_with_buffer(f0, n0, f1, n1, f_b, r);
    I f0_0; I f0_1; I f1_0; I f1_1;
    N n0_0; N n0_1; N n1_0; N n1_1;
    if (n0 < n1)
        merge_n_step_0(
            f0, n0, f1, n1, r,
            f0_0, n0_0, f0_1, n0_1,
            f1_0, n1_0, f1_1, n1_1);
    else
        merge_n_step_1(
            f0, n0, f1, n1, r,
            f0_0, n0_0, f0_1, n0_1,
            f1_0, n1_0, f1_1, n1_1);
        merge_n_adaptive(
            f0_0, n0_0, f0_1, n0_1,
            f_b, n_b, r);
    return
        merge_n_adaptive(
            f1_0, n1_0, f1_1, n1_1,
            f_b, n_b, r);
}

template<MutableForwardIterator I, MutableForwardIterator B>
auto sort_n_adaptive(I f, DistanceType<I> n, B f_b, DistanceType<B> n_b, Relation r)
    __requires(ValueType<I> == ValueType<B> && ValueType<I> == Domain<decltype(r)>)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    auto h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_adaptive(f, h, f_b, n_b, r);
    sort_n_adaptive(m, n - h, f_b, n_b, r);
    return merge_n_adaptive(f, h, m, n - h, f_b, n_b, r);
}

template<MutableForwardIterator I>
I sort_n(I f, DistanceType<I> n, Relation r)
    __requires(ValueType<I> == Domain<decltype(r)>)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<ValueType<I>> b{half_nonnegative(n)};
    return sort_n_adaptive(f, n, begin(b), size(b), r);
}


//
//  Chapter 12. Composite objects
//


// pair type: see Chapter 1 of this file


// Exercise 12.1: less< pair<T0, T1>> using less<T0> and less<T1>


// triple type: see Chapter 1 of this file


// Exercise 12.2: triple type


// array_k type

template<int k, Regular T>
    __requires(0 < k && k <= MaximumValue(int) / sizeof(T))
struct array_k
{
    T a[k];
    T& operator[](int i)
    {
        // Precondition: $0 \leq i < \func{size}(x)$
        return a[i];
    }
};

template<int k, Regular T>
struct size_value<array_k<k, T>>
{
    static const int value = k;
};

template<int k, Regular T>
struct iterator_type<array_k<k, T>>
{
    using type = pointer(T);
};

template<int k, Regular T>
struct value_type< array_k<k, T>>
{
    using type = T;
};

template<int k, Regular T>
struct size_type<array_k<k, T>>
{
    using type = DistanceType<pointer(T)>;
};

template<int k, Regular T>
    __requires(0 < k && k <= MaximumValue(int) / sizeof(T))
struct underlying_type<array_k<k, T>>
{
    using type = array_k<k, UnderlyingType<T>>;
};

template<int k>
auto begin(array_k<k, Regular>& x) -> pointer(Regular)
{
    return addressof(x.a[0]);
}

template<int k, Regular T>
auto begin(const array_k<k, T>& x) -> const pointer(T)
{
    return addressof(x.a[0]);
}

template<int k, Regular T>
auto end(array_k<k, T>& x) -> pointer(T)
{
    return begin(x) + k;
}

template<int k, Regular T>
auto end(const array_k<k, T>& x) -> const pointer(T)
{
    return begin(x) + k;
}

template<int k, Regular T>
bool operator==(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_equal(begin(x), end(x), begin(y), end(y));
}

template<int k, Regular T>
bool operator<(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_less(begin(x), end(x), begin(y), end(y));
}

template<int k, Regular T>
int size(const array_k<k, T>&)
{
    return k;
}

template<int k, Regular T>
bool empty(const array_k<k, T>&)
{
    return false;
}


// concept Linearizeable

//  Since we already defined ValueType for any (regular) T,
//  C++ will not let us define it for any linearizable T like this:

// template<typename W>
//     __requires(Linearizable(W))
// struct value_type
// {
//     using type = ValueType<IteratorType<W>>;
// };

// Instead, each type W that models Linearizable must provide
//      the corresponding specialization of value_type

bool linearizable_equal(const Linearizable& x, const Linearizable& y)
{
    return lexicographical_equal(begin(x), end(x), begin(y), end(y));
}

bool linearizable_ordering(const Linearizable& x, const Linearizable& y)
{
    return lexicographical_less(begin(x), end(x), begin(y), end(y));
}

auto size(const Linearizable& x)
{
    return end(x) - begin(x);
}

bool empty(const Linearizable& x)
{
    return begin(x) == end(x);
}


// type bounded_range
// model Linearizable(bounded_range)

template<ReadableIterator I>
struct bounded_range {
    I f;
    I l;
    bounded_range() {}
    bounded_range(const I& f, const I& l) : f{f}, l{l} {}
    auto operator[](DistanceType<I> i) -> const ValueType<I>&
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<ReadableIterator I>
struct iterator_type<bounded_range<I>>
{
    using type = I;
};

template<ReadableIterator I>
struct value_type<bounded_range<I>>
{
    using type = ValueType<I>;
};

template<ReadableIterator I>
struct size_type<bounded_range<I>>
{
    using type = DistanceType<I>;
};

auto begin(const bounded_range<ReadableIterator>& x) { return x.f; }

auto end(const bounded_range<ReadableIterator>& x) { return x.l; }

bool operator==(
    const bounded_range<ReadableIterator>& x, const bounded_range<ReadableIterator>& y
)
{
    return begin(x) == begin(y) && end(x) == end(y);
}

template<ReadableIterator I>
struct less<bounded_range<I>>
{
    bool operator()(const bounded_range<I>& x, const bounded_range<I>& y)
    {
        less<I> less_I;
        return
            less_I(begin(x), begin(y)) ||
            (!less_I(begin(y), begin(x)) && less_I(end(x), end(y)));
    }
};


// type counted_range
// model Linearizable(counted_range)

template<ReadableIterator I> // should it be ForwardIterator?
struct counted_range {
    using N = DistanceType<I>;
    I f;
    N n;
    counted_range() {}
    counted_range(I f, N n) : f{f}, n{n} {}
    auto operator[](int i) -> const ValueType<I>&
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<ReadableIterator I>
struct iterator_type<counted_range<I>>
{
    using type = I;
};

template<ReadableIterator I>
struct value_type<counted_range<I>>
{
    using type = ValueType<I>;
};

template<ReadableIterator I>
struct size_type<counted_range<I>>
{
    using type = DistanceType<I>;
};

auto begin(const counted_range<ReadableIterator>& x) { return x.f; }

auto end(const counted_range<ReadableIterator>& x) { return x.f + x.n; }

auto size(const counted_range<ReadableIterator>& x) { return x.n; }

bool empty(counted_range<ReadableIterator>& x) { return size(x) == 0; }

bool operator==(
    const counted_range<ReadableIterator>& x, const counted_range<ReadableIterator>& y
)
{
    return begin(x) == begin(y) && size(x) == size(y);
}

template<ReadableIterator I>
struct less<counted_range<I>>
{
    bool operator()(const counted_range<I>& x, const counted_range<I>& y)
    {
        less<I> less_I;
        return
            less_I(begin(x), begin(y)) ||
            (!less_I(begin(y), begin(x)) && size(x) < size(y));
    }
};


// concept Position(T) means
//     BaseType : Position -> Linearizable
//  /\ IteratorType : Position -> Iterator
//  /\ ValueType : Position -> Regular
//         T |- ValueType<IteratorType<T>>
//  /\ SizeType : Position -> Integer
//         T |- SizeType(IteratorType<T>)
//  /\ base : T -> BaseType<T>
//  /\ current : T -> IteratorType<T>
//  /\ begin : T -> IteratorType<T>
//         x |- begin(base(x))
//  /\ end : T -> IteratorType<T>
//         x |- end(base(x))


// concept DynamicSequence(T) means
//     Sequence(T)
//  /\ T supports insert and erase


// concept InsertPosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model InsertPosition(before) /\ InsertPosition(after) /\
//       InsertPosition(front) /\ InsertPosition(back)


// concept ErasePosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model ErasePosition(before) /\ ErasePosition(after) /\
//       ErasePosition(front) /\ ErasePosition(back) /\
//       ErasePosition(at)

template<DynamicSequence S>
struct before
{
    using I = IteratorType<S>;
    pointer(S) s;
    I i;
    before(S& s, I i) : s{&s}, i{i} {}
};

template<DynamicSequence S>
struct base_type<before<S>>
{
    using type = S;
};

template<DynamicSequence S>
struct iterator_type<before<S>>
{
    using type = IteratorType<S>;
};

template<DynamicSequence S>
struct value_type<before<S>>
{
    using type = ValueType<S>;
};

template<DynamicSequence S>
struct size_type<before<S>>
{
    using type = DistanceType<IteratorType<S>>;
};

template<DynamicSequence S>
auto base(before<S>& p) -> S&
{
    return deref(p.s);
}

auto current(before<DynamicSequence>& p)
{
    return p.i;
}

auto begin(before<DynamicSequence>& p)
{
    return begin(base(p));
}

auto end(before<DynamicSequence>& p)
{
    return end(base(p));
}

template<DynamicSequence S>
struct after
{
    using I = IteratorType<S>;
    pointer(S) s;
    I i;
    after(S& s, I i) : s{&s}, i{i} {}
};

template<DynamicSequence S>
struct base_type<after<S>>
{
    using type = S;
};

template<DynamicSequence S>
struct iterator_type<after<S>>
{
    using type = IteratorType<S>;
};

template<DynamicSequence S>
struct value_type<after<S>>
{
    using type = ValueType<S>;
};

template<DynamicSequence S>
struct size_type<after<S>>
{
    using type = DistanceType<IteratorType<S>>;
};

template<DynamicSequence S>
auto base(after<S>& p) -> S&
{
    return deref(p.s);
}

auto current(after<DynamicSequence>& p)
{
    return p.i;
}

auto begin(after<DynamicSequence>& p)
{
    return begin(base(p));
}

auto end(after<DynamicSequence>& p)
{
    return end(base(p));
}

template<DynamicSequence S>
struct front
{
    pointer(S) s;
    front(S& s) : s{&s} {}
};

template<DynamicSequence S>
struct base_type<front<S>>
{
    using type = S;
};

template<DynamicSequence S>
struct iterator_type<front<S>>
{
    using type = IteratorType<S>;
};

template<DynamicSequence S>
struct value_type<front<S>>
{
    using type = ValueType<S>;
};

template<DynamicSequence S>
struct size_type<front<S>>
{
    using type = DistanceType<IteratorType<S>>;
};

template<DynamicSequence S>
auto base(front<S>& p) -> S&
{
    return deref(p.s);
}

auto current(front<DynamicSequence>& p)
{
    return begin(p);
}

auto begin(front<DynamicSequence>& p)
{
    return begin(base(p));
}

auto end(front<DynamicSequence>& p)
{
    return end(base(p));
}

template<DynamicSequence S>
struct back
{
    pointer(S) s;
    back(S& s) : s{&s} {}
};

template<DynamicSequence S>
struct base_type<back<S>>
{
    using type = S;
};

template<DynamicSequence S>
struct iterator_type<back<S>>
{
    using type = IteratorType<S>;
};

template<DynamicSequence S>
struct value_type<back<S>>
{
    using type = ValueType<S>;
};

template<DynamicSequence S>
struct size_type<back<S>>
{
    using type = DistanceType<IteratorType<S>>;
};

template<DynamicSequence S>
auto base(back<S>& p) -> S&
{
    return deref(p.s);
}

auto current(back<DynamicSequence>& p)
{
    return end(p);
}

auto begin(back<DynamicSequence>& p)
{
    return begin(base(p));
}

auto end(back<DynamicSequence>& p)
{
    return end(base(p));
}

template<DynamicSequence S>
struct at
{
    using I = IteratorType<S>;
    pointer(S) s;
    I i;
    at(S& s, I i) : s{&s}, i{i} {}
};

template<DynamicSequence S>
struct base_type<at<S>>
{
    using type = S;
};

template<DynamicSequence S>
struct iterator_type<at<S>>
{
    using type = IteratorType<S>;
};

template<DynamicSequence S>
struct value_type<at<S>>
{
    using type = ValueType<S>;
};

template<DynamicSequence S>
struct size_type<at<S>>
{
    using type = DistanceType<IteratorType<S>>;
};

template<DynamicSequence S>
auto base(at<S>& p) -> S&
{
    return deref(p.s);
}

auto current(at<DynamicSequence>& p)
{
    return p.i;
}

auto begin(at<DynamicSequence>& p)
{
    return begin(base(p));
}

auto end(at<DynamicSequence>& p)
{
    return end(base(p));
}


// type insert_iterator
// model Iterator(insert_iterator)

template<InsertPosition P>
struct insert_iterator
{
    using I = insert_iterator;
    P p;
    insert_iterator() {}
    insert_iterator(const P& p) : p{p} {}
    void operator=(const ValueType<P>& x) { p = insert(p, x); }
};

template<InsertPosition P>
struct iterator_type<insert_iterator<P>>
{
    using type = IteratorType<P>;
};

template<InsertPosition P>
struct value_type<insert_iterator<P>>
{
    using type = ValueType<P>;
};

auto sink(insert_iterator<InsertPosition>& i)
{
    return i;
}

auto successor(const insert_iterator<InsertPosition>& x)
{
    return x;
}

auto insert_range(InsertPosition p, const Linearizable& w)
{
    return copy(begin(w), end(w), insert_iterator<decltype(p)>(p)).p;
}

template<InsertPosition P, ReadableIterator I>
auto insert_range(P p, counted_range<I> w) -> pair<P, I>
{
    auto io = copy_n(begin(w), size(w), insert_iterator<P>(p));
    return pair<P, I>{io.m1.p, io.m0};
}

template<DynamicSequence S>
void dynamic_sequence_construction(S& s, const Linearizable& w)
{
    construct(s);
    S tmp;
    insert_range(after<S>(tmp, end(tmp)), w);
    swap(s, tmp);
}


// type slist
// model DynamicSequence(slist)

template<Regular T>
struct slist_node
{
    T value;
    pointer(slist_node) forward_link;
    slist_node(const T& v, pointer(slist_node) f) : value{v}, forward_link{f} {}
};

static int slist_node_count = 0; /* ***** TESTING ***** */

template<Regular T>
struct slist_iterator
{
    pointer(slist_node<T>) p;
    slist_iterator() : p{0} {}
    slist_iterator(pointer(slist_node<T>) p) : p{p} {}
};

template<Regular T>
struct value_type<slist_iterator<T>>
{
    using type = T;
};

template<Regular T>
struct distance_type<slist_iterator<T>>
{
    using type = DistanceType<slist_node<T>*>;
};

template<Regular T>
struct iterator_concept<slist_iterator<T>>
{
    using __concept = forward_iterator_tag;
};

template<Regular T>
auto successor(const slist_iterator<T>& i)
{
    return slist_iterator<T>(source(i.p).forward_link);
}

void set_link_forward(LinkedForwardIterator i, LinkedForwardIterator j)
{
    forward_linker<decltype(i)>()(i, j);
}

bool operator==(slist_iterator<Regular> i, slist_iterator<Regular> j)
{
    return i.p == j.p;
}

template<Regular T>
struct less<slist_iterator<T>>
{
    bool operator()(slist_iterator<T> i, slist_iterator<T> j)
    {
        return i.p < j.p;
    }
};

auto source(slist_iterator<Regular> i) -> const Regular&
{
    return source(i.p).value;
}

auto sink(slist_iterator<Regular> i) -> Regular&
{
    return sink(i.p).value;
}

auto deref(slist_iterator<Regular> i) -> Regular&
{
    return sink(i.p).value;
}

auto erase_first(slist_iterator<Regular> i)
{
    auto j = successor(i);
    destroy(sink(i));
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

template<Regular T, typename U>
auto erase_first(slist_iterator<T> i, U& u)
    requires Destroyable<T, U>()
{
    auto j = successor(i);
    destroy(sink(i), u);
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

void erase_after(slist_iterator<Regular> i)
{
    set_successor(i, erase_first(successor(i)));
}

template<Regular T, typename U>
void erase_after(slist_iterator<T> i, U& u)
    requires Destroyable<T, U>()
{
    set_successor(i, erase_first(successor(i), u));
}

template<Regular T>
struct slist
{
    slist_iterator<T> first;
    slist() : first{0} {}
    slist(const slist& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    template<Linearizable W>
    slist(const W& w)
        __requires(T == ValueType<W>)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(slist x)
    {
        swap(deref(this), x);
    }
    auto operator[](DistanceType<slist_iterator<T>> i) -> T&
    {
        return deref(first + i);
    }
    ~slist()
    {
        erase_all(sink(this));
    }
};

template<Regular T>
struct iterator_type<slist<T>>
{
    using type = slist_iterator<T>;
};

template<Regular T>
struct value_type<slist<T>>
{
    using type = T;
};

template<Regular T>
struct size_type<slist<T>>
{
    using type = DistanceType<IteratorType<slist<T>>>;
};

template<Regular T>
struct underlying_type<slist<T>>
{
    using type = slist_iterator<T>; // or IteratorType<slist<T>>
};

auto begin(const slist<Regular>& x)
{
    return x.first;
}

template<Regular T>
auto end(const slist<T>&)
{
    return slist_iterator<T>{};
}

// size, empty subsumed by definitions for Linearizeable

void erase_all(slist<Regular>& x)
{
    while (!empty(x)) x.first = erase_first(begin(x));
}

bool operator==(const slist<Regular>& x, const slist<Regular>& y)
{
    return linearizable_equal(x, y);
}

bool operator<(const slist<Regular>& x, const slist<Regular>& y)
{
    return linearizable_ordering(x, y);
}

template<Regular T, typename U>
auto insert(after<slist<T>> p, const U& u)
    requires Constructible<T, U>()
{
    slist_node_count = successor(slist_node_count);
    slist_iterator<T> i{reinterpret_cast<slist_node<T>*>(malloc(sizeof(slist_node<T>)))};
    construct(sink(i), u);
    if (current(p) == end(p)) {
        set_link_forward(i, begin(p));
        base(p).first = i;
    } else {
        set_link_forward(i, successor(current(p)));
        set_link_forward(current(p), i);
    }
    return after<slist<T>>{base(p), i};
}

template<Regular T>
void reverse(slist<T>& x)
{
    using I = IteratorType<slist<T>>;
    x.first = reverse_append(begin(x), end(x), end(x), forward_linker<I>());
}

template<Regular T, UnaryPredicate P>
void partition(slist<T>& x, slist<T>& y, P p)
    __requires(Domain<P> == T)
{
    using I = IteratorType<slist<T>>;
    auto pp = partition_linked(begin(x), end(x), p, forward_linker<I>());
    x.first = pp.m0.m0;
    if (pp.m0.m0 != end(x))
        forward_linker<I>()(pp.m0.m1, end(x));
    if (pp.m1.m0 != end(x)) {
        forward_linker<I>()(pp.m1.m1, begin(y));
        y.first = pp.m1.m0;
    }
}

template<Regular T>
void merge(slist<T>& x, slist<T>& y, Regular r)
    __requires(Domain<decltype(r)> == T)
{
    // Precondition: $\func{weak\_ordering}(r)$
    using I = IteratorType<slist<T>>;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    x.first = merge_linked_nonempty(
        begin(x), end(x), begin(y), end(y), r, forward_linker<I>()).m0;
    y.first = end(y); // former nodes of y now belong to x
}

template<Regular T>
void sort(slist<T>& x, Relation r)
    __requires(Domain<decltype(r)> == T)
{
    // Precondition: $\func{weak\_ordering}(r)$
    using I = IteratorType<slist<T>>;
    auto p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    x.first = p.m0;
}


// type list
// model DynamicSequence(list)

template<Regular T>
struct list_node
{
    T value;
    pointer(list_node) forward_link;
    pointer(list_node) backward_link;
    list_node(const T& v, pointer(list_node) f, pointer(list_node) b)
        : value{v}, forward_link{f}, backward_link{b}
    {}
};

static int list_node_count = 0; /* ***** TESTING ***** */

template<Regular T>
struct list_iterator
{
    pointer(list_node<T>) p;
    list_iterator() : p{0} {}
    list_iterator(pointer(list_node<T>) p) : p{p} {}
};

template<Regular T>
struct value_type<list_iterator<T>>
{
    using type = T;
};

template<Regular T>
struct distance_type<list_iterator<T>>
{
    using type = DistanceType<list_node<T>*>;
};

template<Regular T>
struct iterator_concept<list_iterator<T>>
{
    using __concept = bidirectional_iterator_tag;
};

template<Regular T>
auto successor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).forward_link);
}

template<Regular T>
auto predecessor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).backward_link);
}

void set_link_backward(LinkedBidirectionalIterator i, LinkedBidirectionalIterator j)
{
    backward_linker<decltype(i)>()(i, j);
}

void set_link_bidirectional(LinkedForwardIterator i, LinkedForwardIterator j)
{
    bidirectional_linker<decltype(i)>()(i, j);
}

bool operator==(list_iterator<Regular> i, list_iterator<Regular> j)
{
    return i.p == j.p;
}

template<Regular T>
struct less<list_iterator<T>>
{
    bool operator()(list_iterator<T> i, list_iterator<T> j)
    {
        return i.p < j.p;
    }
};

auto source(list_iterator<Regular> i) -> const Regular&
{
    return source(i.p).value;
}

auto sink(list_iterator<Regular> i) -> Regular&
{
    return sink(i.p).value;
}

auto deref(list_iterator<Regular> i) -> Regular&
{
    return sink(i.p).value;
}

void erase(list_iterator<Regular> i)
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i));
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<Regular T, typename U>
void erase(list_iterator<T> i, U& u)
    requires Destroyable<T, U>()
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i), u);
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<Regular T>
struct list
{
    list_iterator<T> dummy;
    list() : dummy{reinterpret_cast<list_node<T>*>(malloc(sizeof(list_node<T>)))}
    {
        // The dummy node's value is never constructed
        set_link_bidirectional(dummy, dummy);
    }
    list(const list& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    list(const Linearizable& w)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(list x)
    {
        swap(deref(this), x);
    }
    auto operator[](DistanceType<list_iterator<T>> i) -> T&
    {
        return deref(begin(deref(this)) + i);
    }
    ~list()
    {
        erase_all(sink(this));
        // We do not destroy the dummy node's value since it was not constructed
        free(dummy.p);
    }
};

template<Regular T>
struct iterator_type<list<T>>
{
    using type = list_iterator<T>;
};

template<Regular T>
struct value_type<list<T>>
{
    using type = T;
};

template<Regular T>
struct size_type<list<T>>
{
    using type = DistanceType<IteratorType<list<T>>>;
};

template<Regular T>
struct underlying_type<list<T>>
{
    using type = list_iterator<T>; // or IteratorType<list<T>>
};

auto begin(const list<Regular>& x)
{
    return successor(x.dummy);
}

auto end(const list<Regular>& x)
{
    return x.dummy;
}

// size, empty subsumed by definitions for Linearizeable

void erase_all(list<Regular>& x)
{
    while (!empty(x)) erase(predecessor(end(x)));
}

bool operator==(const list<Regular>& x, const list<Regular>& y)
{
    return linearizable_equal(x, y);
}

bool operator<(const list<Regular>& x, const list<Regular>& y)
{
    return linearizable_ordering(x, y);
}

template<Regular T, typename U>
auto insert(list_iterator<T> j, const U& u)
    requires Constructible<T, U>()
{
    list_node_count = successor(list_node_count);
    list_iterator<T> i{(list_node<T>*)malloc(sizeof(list_node<T>))};
    construct(sink(i), u);
    set_link_bidirectional(predecessor(j), i);
    set_link_bidirectional(i, j);
    return i;
}

template<Regular T, typename U>
auto insert(after<list<T>> p, const U& u)
    requires Constructible<T, U>()
{
    return after<list<T>>(base(p), insert(successor(current(p)), u));
}

template<Regular T>
void reverse(list<T>& x)
{
    using I = IteratorType<list<T>>;
    I i = reverse_append(begin(x), end(x), end(x), bidirectional_linker<I>());
    set_link_bidirectional(x.dummy, i);
}

template<Regular T>
void partition(list<T>& x, list<T>& y, UnaryPredicate p)
    __requires(Domain<decltype(p)> == T)
{
    using I = IteratorType<list<T>>;
    bidirectional_linker<I> set_link;
    auto pp = partition_linked(begin(x), end(x), p, set_link);
    set_link(pp.m0.m1, x.dummy);
    set_link(x.dummy, pp.m0.m0);
    if (pp.m1.m0 != end(x)) {
        set_link(pp.m1.m1, begin(y));
        set_link(y.dummy, pp.m1.m0);
    }
}

template<Regular T>
void merge(list<T>& x, list<T>& y, Regular r)
    __requires(Domain<decltype(r)> == T)
{
    // Precondition: $\func{weak\_ordering}(r)$
    using I = IteratorType<list<T>>;
    bidirectional_linker<I> set_link;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    auto p = merge_linked_nonempty(begin(x), end(x), begin(y), end(y), r, set_link);
    set_link(x.dummy, p.m0);
    set_link(find_last(p.m0, p.m1), x.dummy);
    set_link(y.dummy, y.dummy); // former nodes of y now belong to x
}

template<Regular T>
void sort(list<T>& x, Relation r)
    __requires(Domain<decltype(r)> == T)
{
    // Precondition: $\func{weak\_ordering}(r)$
    using I = IteratorType<list<T>>;
    auto p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    // See the end of section 8.3 of Elements of Programming
    // for the explanation of this relinking code:
    bidirectional_linker<I>()(x.dummy, p.m0);
    I f = p.m0;
    while (f != p.m1) {
        backward_linker<I>()(f, successor(f));
        f = successor(f);
    }
}


// concept BinaryTree means ...


// type stree
// model BinaryTree(stree)

template<Regular T>
struct stree_node
{
    using Link = pointer(stree_node);
    T value;
    Link left_successor_link;
    Link right_successor_link;
    stree_node() : left_successor_link{0}, right_successor_link{0} {}
    stree_node(T v, Link l = 0, Link r = 0) :
        value{v}, left_successor_link{l}, right_successor_link{r}
    {}
};

template<Regular T>
struct stree_coordinate
{
    pointer(stree_node<T>) ptr;
    stree_coordinate() : ptr{0} {}
    stree_coordinate(pointer(stree_node<T>) ptr) : ptr{ptr} {}
};

template<Regular T>
struct value_type<stree_coordinate<T>>
{
    using type = T;
};

template<Regular T>
struct weight_type<stree_coordinate<T>>
{
    using type = DistanceType<pointer(stree_node<T>)>;
};

template<Regular T>
bool empty(stree_coordinate<T> c)
{
    using I = pointer(stree_node<T>);
    return c.ptr == I{0};
}

template<Regular T>
auto left_successor(stree_coordinate<T> c) -> stree_coordinate<T>
{
    return source(c.ptr).left_successor_link;
}

template<Regular T>
auto right_successor(stree_coordinate<T> c) -> stree_coordinate<T>
{
    return source(c.ptr).right_successor_link;
}

bool has_left_successor(stree_coordinate<Regular> c)
{
    return !empty(left_successor(c));
}

bool has_right_successor(stree_coordinate<Regular> c)
{
    return !empty(right_successor(c));
}

void set_left_successor(stree_coordinate<Regular> c, stree_coordinate<Regular> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
}

void set_right_successor(stree_coordinate<Regular> c, stree_coordinate<Regular> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
}

bool operator==(stree_coordinate<Regular> c0, stree_coordinate<Regular> c1)
{
    return c0.ptr == c1.ptr;
}

template<Regular T>
auto source(stree_coordinate<T> c) -> const T&
{
    return source(c.ptr).value;
}

template<Regular T>
auto sink(stree_coordinate<T> c) -> T&
{
    return sink(c.ptr).value;
}

static int stree_node_count = 0; /* ***** TESTING ***** */

template<Regular T>
struct stree_node_construct
{
    using C = stree_coordinate<T>;
    stree_node_construct() {}
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++stree_node_count;
        return C{new stree_node<T>(x, l.ptr, r.ptr)};
    }
    C operator()(C c)
    {
        return (*this)(source(c), left_successor(c), right_successor(c));
    }
    C operator()(C c, C l, C r)
    {
        return (*this)(source(c), l, r);
    }
};

template<Regular T>
struct stree_node_destroy
{
    stree_node_destroy() {}
    void operator()(stree_coordinate<T> i)
    {
        --stree_node_count;
        delete i.ptr;
    }
};

void bifurcate_erase(BifurcateCoordinate c, TreeNodeDeleter node_delete)
{
    using C = decltype(c);
    if (empty(c)) return;
    auto stack = C{0}; // chained through left_successor
    while (true) {
        auto left = left_successor(c);
        auto right = right_successor(c);
        if (!empty(left)) {
            if (!empty(right)) {
                set_left_successor(c, stack);
                stack = c;
            } else
                node_delete(c);
            c = left;
        } else if (!empty(right)) {
            node_delete(c);
            c = right;
        } else {
            node_delete(c);
            if (!empty(stack)) {
                c = stack;
                stack = left_successor(stack);
                set_left_successor(c, C{0});
           } else return;
        }
    }
}

/*
   The next function is based on MAKECOPY in this paper:

   K. P. Lee.
   A linear algorithm for copying binary trees using bounded workspace.
   Commun. ACM 23, 3 (March 1980), 159-162. DOI=10.1145/358826.358835
   http://doi.acm.org/10.1145/358826.358835
*/

template<EmptyLinkedBifurcateCoordinate C, TreeNodeConstructor Cons>
auto bifurcate_copy(C c)
    __requires(NodeType(decltype(c)) == NodeType(Cons))
{
    Cons construct_node;
    if (empty(c)) return c;                 // Us      / Lee
    auto stack = construct_node(c, c, C{}); // stack   / V'
    auto c_new = stack;                     // c\_new  / COPY
    while (!empty(stack)) {                 // empty() / null
        c = left_successor(stack);          // c       / V
        auto l = left_successor(c);
        auto r = right_successor(c);
        auto top = stack;
        if (!empty(l)) {
            if (!empty(r)) {
                r = construct_node(r, r, right_successor(stack));
                stack = construct_node(l, l, r);
            }
            else  {
                r = C{};
                stack = construct_node(l, l, right_successor(stack));
            }
            l = stack;
        } else if (!empty(r)) {
            stack = construct_node(r, r, right_successor(stack));
            r = stack;
        } else
            stack = right_successor(stack);
        set_right_successor(top, r);
        set_left_successor(top, l);
    }
    return c_new;
}

template<Regular T>
struct stree
{
    using C = stree_coordinate<T>;
    using Cons = stree_node_construct<T>;
    C root;
    stree() : root(0) {}
    stree(T x) : root{Cons{}(x)} {}
    stree(T x, const stree& left, const stree& right) : root{Cons{}(x)}
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    stree(const stree& x) : root(bifurcate_copy<C, Cons>(x.root)) {}
    ~stree() { bifurcate_erase(root, stree_node_destroy<T>()); }
    void operator=(stree x) { swap(root, x.root); }
};

template<Regular T>
struct coordinate_type<stree<T>>
{
    using type = stree_coordinate<T>;
};

template<Regular T>
struct value_type<stree<T>>
{
    using type = T;
};

template<Regular T>
struct weight_type<stree<T>>
{
    using type = WeightType<CoordinateType<stree<T>>>;
};

auto begin(const stree<Regular>& x)
{
    return x.root;
}

bool empty(const stree<Regular>& x)
{
    return empty(x.root);
}

template<Regular T>
bool operator==(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return empty(y);
    if (empty(y)) return false;
    return bifurcate_equivalent_nonempty(begin(x), begin(y), equal<T>());
}

template<Regular T>
bool operator<(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return !empty(y);
    if (empty(y)) return false;
    less<T> lt;
    return 1 == bifurcate_compare_nonempty(
        begin(x), begin(y),
        comparator_3_way<less<T>>(lt));
}

template<Regular T, typename Proc>
void traverse(stree<T>& x, Proc proc)
    requires Arity<Proc> == 2
    __requires(Procedure(Proc) && visit == InputType<Proc, 0> && CoordinateType<stree<T>> == InputType<Proc, 1>)
{
    traverse_nonempty(begin(x), proc);
}


// type tree
// model BinaryTree(tree)

template<Regular T>
struct tree_node
{
    using Link = pointer(tree_node);
    T value;
    Link left_successor_link;
    Link right_successor_link;
    Link predecessor_link;
    tree_node()
        : left_successor_link{0}, right_successor_link{0}, predecessor_link{0}
    {}
    tree_node(T v, Link l = 0, Link r = 0, Link p = 0)
        : value{v}, left_successor_link{l}, right_successor_link{r}, predecessor_link{p}
    {}
};

template<Regular T>
struct tree_coordinate
{
    pointer(tree_node<T>) ptr;
    tree_coordinate() : ptr{0} {}
    tree_coordinate(pointer(tree_node<T>) ptr) : ptr{ptr} {}
};

template<Regular T>
struct value_type<tree_coordinate<T>>
{
    using type = T;
};

template<Regular T>
struct weight_type<tree_coordinate<T>>
{
    using type = DistanceType<pointer(tree_node<T>)>;
};

template<Regular T>
bool empty(tree_coordinate<T> c)
{
    return c.ptr == 0;
}

template<Regular T>
auto left_successor(tree_coordinate<T> c) -> tree_coordinate<T>
{
    return source(c.ptr).left_successor_link;
}

template<Regular T>
auto right_successor(tree_coordinate<T> c) -> tree_coordinate<T>
{
    return source(c.ptr).right_successor_link;
}

bool has_left_successor(tree_coordinate<Regular> c)
{
    return !empty(left_successor(c));
}

bool has_right_successor(tree_coordinate<Regular> c)
{
    return !empty(right_successor(c));
}

template<Regular T>
auto predecessor(tree_coordinate<T> c) -> tree_coordinate<T>
{
    return source(c.ptr).predecessor_link;
}

bool has_predecessor(tree_coordinate<Regular> c)
{
    return !empty(predecessor(c));
}

void set_predecessor(tree_coordinate<Regular> c, tree_coordinate<Regular> p)
{
    sink(c.ptr).predecessor_link = p.ptr;
}

void set_left_successor(tree_coordinate<Regular> c, tree_coordinate<Regular> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
    if (!empty(l)) set_predecessor(l, c);
}

void set_right_successor(tree_coordinate<Regular> c, tree_coordinate<Regular> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
    if (!empty(r)) set_predecessor(r, c);
}

bool operator==(tree_coordinate<Regular> c0, tree_coordinate<Regular> c1)
{
    return c0.ptr == c1.ptr;
}

auto source(tree_coordinate<Regular> c) -> const Regular&
{
    return source(c.ptr).value;
}

auto sink(tree_coordinate<Regular> c) -> Regular&
{
    return sink(c.ptr).value;
}

static int tree_node_count = 0; /* ***** TESTING ***** */

template<Regular T>
struct tree_node_construct
{
    using C = tree_coordinate<T>;
    tree_node_construct() {}
    auto operator()(T x, C l = C(0), C r = C(0))
    {
        ++tree_node_count;
        return C(new tree_node<T>(x, l.ptr, r.ptr));
    }
    auto operator()(C c)
    {
        return (*this)(source(c), left_successor(c), right_successor(c));
    }
    auto operator()(C c, C l, C r)
    {
        return (*this)(source(c), l, r);
    }
};

template<Regular T>
struct tree_node_destroy
{
    tree_node_destroy() {}
    void operator()(tree_coordinate<T> i)
    {
        --tree_node_count;
        delete i.ptr;
    }
};

template<Regular T>
struct tree
{
    using C = tree_coordinate<T>;
    using Cons = tree_node_construct<T>;
    C root;
    tree() : root{0} {}
    tree(T x) : root{Cons()(x)} {}
    tree(T x, const tree& left, const tree& right) : root{Cons()(x)}
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    tree(const tree& x) : root{bifurcate_copy<C, Cons>(x.root)} {}
    ~tree()
    {
        bifurcate_erase(root, tree_node_destroy<T>());
    }
    void operator=(tree x)
    {
        swap(root, x.root);
    }
};

template<Regular T>
struct coordinate_type<tree<T>>
{
    using type = tree_coordinate<T>;
};

template<Regular T>
struct value_type<tree<T>>
{
    using type = ValueType<CoordinateType<tree<T>>>;
};

template<Regular T>
struct weight_type<tree<T>>
{
    using type = WeightType<CoordinateType<tree<T>>>;
};

auto begin(const tree<Regular>& x)
{
    return x.root;
}

bool empty(const tree<Regular>& x)
{
    return empty(x.root);
}

bool operator==(const tree<Regular>& x, const tree<Regular>& y)
{
    return bifurcate_equal(begin(x), begin(y));
}

bool operator<(const tree<Regular>& x, const tree<Regular>& y)
{
    return bifurcate_less(begin(x), begin(y));
}

template<Regular T, typename Proc>
void traverse(tree<T>& x, Proc proc)
    requires Arity<Proc> == 2
    __requires(Procedure(Proc) &&
        visit == InputType<Proc, 0> &&
        CoordinateType<tree<T>> == InputType<Proc, 1>)
{
    traverse(begin(x), proc);
}


// type array
// model DynamicSequence(array)

template<Regular T>
struct array_prefix
{
    pointer(T) m;
    pointer(T) l;
    T a;
    // Invariant: $[addressof(a), m)$ are constructed elements
    // Invariant: $[m, l)$ are unconstructed (reserve) elements
};

template<Regular T>
auto allocate_array(DistanceType<T*> n)
{
    using P = pointer(array_prefix<T>);
    if (zero(n)) return P(0);
    auto bsize = int(predecessor(n)) * sizeof(T);
    auto p = P(malloc(sizeof(array_prefix<T>) + bsize));
    pointer(T) f = &sink(p).a;
    sink(p).m = f;
    sink(p).l = f + n;
    return p;
}

void deallocate_array(pointer(array_prefix<Regular>) p)
{
    free(p);
}

template<Regular T>
struct array
{
    using N = DistanceType<IteratorType<array<T>>>;
    pointer(array_prefix<T>) p;
    array() : p{0} {}
    array(N c) : p{allocate_array<T>(c)} {} // size is 0 and capacity is c
    array(N s, N c, const T& x)
        : p{allocate_array<T>(c)} // size is s, capacity is c, all elements equal to x
    {
        while (!zero(s)) { push(sink(this), x); s = predecessor(s); }
    }
    array(const array& x) : p(allocate_array<T>(size(x)))
    {
        insert_range(back<array<T>>(sink(this)), x);
    }
    template<Linearizable W>
    array(const W& w) : p(allocate_array<T>(0))
        __requires(T == ValueType<W>)
    {
        insert_range(back<array<T>>(sink(this)), w);
    }
    template<ReadableIterator I>
    array(const counted_range<I>& w) : p(allocate_array<T>(size(w)))
        __requires(T == ValueType<I>)
    {
        insert_range(back<array<T>>(sink(this)), w);
    }
    void operator=(array x)
    {
        swap(deref(this), x);
    }
    auto operator[](N i) -> T&
    {
        return deref(begin(deref(this)) + i);
    }
    auto operator[](N i) const -> const T&
    {
        return deref(begin(deref(this)) + i);
    }
    ~array()
    {
        erase_all(sink(this));
    }
};

template<Regular T>
struct iterator_type<array<T>>
{
    using type = pointer(T);
};

template<Regular T>
struct value_type<array<T>>
{
    using type = T;
};

template<Regular T>
struct size_type<array<T>>
{
    using type = DistanceType<IteratorType<array<T>>>;
};

template<Regular T>
struct underlying_type<array<T>>
{
    using type = struct { pointer(array_prefix<T>) p; };
};

template<Regular T>
auto begin(const array<T>& x)
{
    using P = pointer(array_prefix<T>);
    using I = IteratorType<array<T>>;
    if (x.p == P{0}) return I{0};
    return I(addressof(source(x.p).a));
}

template<Regular T>
auto end(const array<T>& x)
{
    using P = pointer(array_prefix<T>);
    using I = IteratorType<array<T>>;
    if (x.p == P{0}) return I{0};
    return I(source(x.p).m);
}

template<Regular T>
auto end_of_storage(const array<T>& x)
{
    using P = pointer(array_prefix<T>);
    using I = IteratorType<array<T>>;
    if (x.p == P{0}) return I{0};
    return I(source(x.p).l);
}

auto capacity(const array<Regular>& x)
{
    return end_of_storage(x) - begin(x);
}

bool full(const array<Regular>& x)
{
    return end(x) == end_of_storage(x);
}

bool operator==(const array<Regular>& x, const array<Regular>& y)
{
    return linearizable_equal(x, y);
}

bool operator<(const array<Regular>& x, const array<Regular>& y)
{
    return linearizable_ordering(x, y);
}

template<Regular T, Regular U>
auto insert(back<array<T>> p, const U& y)
    requires Constructible<T, U>()
{
    using N = DistanceType<IteratorType<array<T>>>;
    auto n = size(base(p));
    if (n == capacity(base(p)))
        reserve(base(p), max(N{1}, n + n));
    construct(sink(source(base(p).p).m), y);
    sink(base(p).p).m = successor(sink(base(p).p).m);
    return p;
}

template<Regular T, Linearizable W>
auto insert_range(before<array<T>> p, const W& w)
    requires Constructible<T, ValueType<W>>()
{
    using I = IteratorType<array<T>>;
    auto o_f = current(p) - begin(p);
    auto o_m = size(p);
    insert_range(back<array<T>>(base(p)), w);
    return before<array<T>>{base(p), rotate(begin(p) + o_f, begin(p) + o_m, end(p))};
}
// Note that for iterators supporting fast subtraction,
// we could write a somewhat faster but also much more complex
// version (complexity mostly dealing with exception safety)

auto erase(back<array<Regular>> x)
{
    --sink(deref(x.s).p).m;
    destroy(sink(source(deref(x.s).p).m));
    if (empty(deref(x.s))) {
        deallocate_array(deref(x.s).p);
        deref(x.s).p = 0;
    }
    return x;
}

template<Regular T>
void erase_all(array<T>& x)
{
    while (!empty(x)) erase(back<array<T>>(x));
}

void swap_basic(Regular& x, Regular& y)
{
    auto tmp = x;
    x = y;
    y = tmp;
}

template<Regular T>
auto underlying_ref(T& x) -> UnderlyingType<T>&
{
    return reinterpret_cast<UnderlyingType<T>&>(x);
}

template<Regular T>
auto underlying_ref(const T& x) -> const UnderlyingType<T>&
{
    return reinterpret_cast<UnderlyingType<T>&>(const_cast<T&>(x));
}

void swap(Regular& x, Regular& y)
{
    auto tmp = underlying_ref(x);
    underlying_ref(x) = underlying_ref(y);
    underlying_ref(y) = tmp;
}


// Exercise 12.9:

template<Iterator I>
struct underlying_iterator
{
    I i;
    underlying_iterator() {}
    underlying_iterator(const I& x) : i{x} {}
};

template<Iterator I>
struct value_type<underlying_iterator<I>>
{
    using type = UnderlyingType<ValueType<I>>;
};

template<Iterator I>
struct distance_type<underlying_iterator<I>>
{
    using type = DistanceType<I>;
};

template<Iterator I>
struct iterator_concept<underlying_iterator<I>>
{
    using __concept = IteratorConcept(I);
};

template<Iterator I>
auto successor(const underlying_iterator<I>& x) -> underlying_iterator<I>
{
    return successor(x.i);
}

template<Iterator I>
auto predecessor(const underlying_iterator<I>& x) -> underlying_iterator<I>
{
    return predecessor(x.i);
}

template<Iterator I>
auto operator+(underlying_iterator<I> x, DistanceType<I> n)
{
    return underlying_iterator<I>(x.i + n);
}

template<Iterator I>
auto operator-(underlying_iterator<I> x, underlying_iterator<I> y)
{
    return x.i - y.i;
}

template<Iterator I>
underlying_iterator<I> operator-(underlying_iterator<I> x, DistanceType<I> n)
{
    return underlying_iterator<I>(x.i - n);
}

bool operator==(
    const underlying_iterator<Iterator>& x, const underlying_iterator<Iterator>& y
)
{
    return x.i == y.i;
}

bool operator<(
    const underlying_iterator<Iterator>& x, const underlying_iterator<Iterator>& y
)
{
    return x.i < y.i;
}

template<Iterator I>
auto source(const underlying_iterator<I>& x) -> const UnderlyingType<ValueType<I>>&
{
    return underlying_ref(source(x.i));
}

template<Iterator I>
auto sink(underlying_iterator<I>& x) -> UnderlyingType<ValueType<I>>&
{
    return underlying_ref(sink(x.i));
}

template<Iterator i>
auto deref(underlying_iterator<i>& x) -> UnderlyingType<ValueType<i>>&
{
    return underlying_ref(deref(x.i));
}

auto original(const underlying_iterator<Iterator>& x)
{
    return x.i;
}


// Project 12.5: here are some more techniques and examples:

template<Regular T>
void reserve_basic(array<T>& x, DistanceType<IteratorType<array<T>>> n)
{
    if (n < size(x) || n == capacity(x)) return;
    array<T> tmp(n);
    insert_range(back<array<T>>(tmp), x);
    swap(tmp, x);
}

template<Regular T>
void reserve(array<T>& x, DistanceType<IteratorType<array<T>>> n)
{
    reserve_basic(reinterpret_cast<array<UnderlyingType<T>>&>(x), n);
}


// In order to adapt algorithms with predicates and relations as
// arguments, we use adapters that cast from the underlying type to the
// original type before calling the predicate or relation:

template<Regular T>
auto original_ref(UnderlyingType<T>& x) -> T&
{
    return reinterpret_cast<T&>(x);
}

template<Regular T>
auto original_ref(const UnderlyingType<T>& x) -> const T&
{
    return reinterpret_cast<const T&>(x);
}

template<Predicate P>
struct underlying_predicate
{
    using U = UnderlyingType<Domain<P>>;
    P p;
    underlying_predicate(P p) : p{p} {}
    bool operator()(const U& x)
    {
        return p(original_ref<Domain<P>>(x));
    }
};

template<Predicate P>
struct input_type<underlying_predicate<P>, 0>
{
    using type = UnderlyingType<Domain<P>>;
};

template<Relation R>
struct underlying_relation
{
    using U = UnderlyingType<Domain<R>>;
    R r;
    underlying_relation(R r) : r{r} {}
    bool operator()(const U& x, const U& y)
    {
        return r(original_ref<Domain<R>>(x), original_ref<Domain<R>>(y));
    }
};

template<Relation R>
struct input_type<underlying_relation<R>, 0>
{
    using type = UnderlyingType<Domain<R>>;
};

template<MutableForwardIterator I>
auto advanced_partition_stable_n(I f, DistanceType<I> n, UnaryPredicate p)
    __requires(ValueType<I> == Domain<decltype(p)>)
{
    using U = underlying_iterator<I>;
    auto tmp = partition_stable_n(U{f}, n, underlying_predicate<decltype(p)>(p));
    return pair<I, I>{original(tmp.m0), original(tmp.m1)};
}

template<MutableForwardIterator I>
auto advanced_sort_n(I f, DistanceType<I> n, Relation r)
    __requires(ValueType<I> == Domain<decltype(r)>)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<UnderlyingType<ValueType<I>>> b{half_nonnegative(n)};
    return original(
        sort_n_adaptive(
            underlying_iterator<I>(f), n, begin(b), size(b),
            underlying_relation<decltype(r)>(r))
        );
}

template<Regular T>
void sort(array<T>& x, Relation r)
    __requires(Domain<decltype(r)> == T)
{
    // Precondition: $\func{weak\_ordering}(r)$
    advanced_sort_n(begin(x), size(x), r);
}

#endif // EOP_EOP
