// Copyright (c) 2014 Alexander A. Stepanov and Daniel E. Rose
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.
//
// This code accompanies the "fM2GP" book:
//
//	From Mathematics to Generic Programming
//	by Alexander Stepanov and Daniel E. Rose
//	Addison-Wesley Professional, 2015
//
// -------------------------------------------------------------------
// ch07.h -- Functions from Chapter 7 of fM2GP.
// -------------------------------------------------------------------

#include <functional>

template <class T, class U>
concept bool Same() {
    return std::is_same<T, U>::value;
}

template <class T, class... Args>
concept bool DefaultConstructible() {
    return requires (Args&& ...args) {
        T{std::forward<Args>(args)...}; // not required to be equality preserving
        new T{std::forward<Args>(args)...}; // not required to be equality preserving
    }
    && requires (const size_t n) {
        new T[n]{}; // Not required to be equality preserving.
    };
}

template <class T>
concept bool Destructible() {
    return requires (T t, const T ct, T* p) {
        { t.~T() } noexcept;
        { &t } -> Same<T*>; // Not required to be equality preserving.
        { &ct } -> Same<const T*>; // Not required to be equality preserving.
        delete p;
        delete[] p;
    };
}

template <class T, class... Args>
concept bool Regular() {
    return DefaultConstructible<T>()
        && Destructible<T>();
}

template <typename T>
concept bool NoncommutativeAdditiveSemigroup() {
    return Regular<T>()
        && requires (const T& a, const T& b) {
            { a + b } -> T
        };
        // associative(+)
}

template <typename T>
concept bool AdditiveSemigroup() {
    return NoncommutativeAdditiveSemigroup<T>();
        // commutative(+)
}

template <typename T>
concept bool MultiplicativeSemigroup() {
    return Regular<T>()
        && requires (const T& a, const T& b) {
            { a * b } -> T
        };
        // associative(*)
}

template <typename T>
concept bool NoncommutativeAdditiveMonoid() {
    return AdditiveSemigroup<T>()
        && requires (const T& a) {
            T{0};
            // identity_element(0, +)
        };
}

template <typename T>
concept bool AdditiveMonoid() {
    return NoncommutativeAdditiveMonoid<T>();
    // commutative(+)
}

template <typename T>
concept bool MultiplicativeMonoid() {
    return MultiplicativeSemigroup<T>()
        && requires (const T& a) {
            T{1};
            // identity_element(1, *)
        };
}

template <typename T>
concept bool NoncommutativeAdditiveGroup() {
    return AdditiveMonoid<T>()
        && requires (const T& a, const T& b) {
            { -a } -> T
            // inverse_operation(unary -, 0, +)
            { a - b } -> T
                // (a, b) -> a + (-b)
        };
}

template <typename T>
concept bool AdditiveGroup() {
    return NoncommutativeAdditiveGroup<T>();
}

template <typename T>
concept bool MultiplicativeGroup() {
    return MultiplicativeMonoid<T>()
        && requires (const T& a, const T& b) {
            // { multiplicative_inverse(a) } -> T
            // inverse_operation(multiplicative_inverse, 1, *)
            { a / b } -> T
                // (a, b) -> a * multiplicative_inverse(b)
        };
}

template <typename I>
concept bool Integer() {
    return std::is_integral<I>::value;
}

template<typename T, int i>
    // requires(FunctionalProcedure(T))
struct input_type;

template<typename T, int i>
using InputType = typename input_type<T, i>::type;

template<typename T>
using Domain = InputType<T, 0>;

#define SemigroupOperation typename
#define MonoidOperation typename
#define GroupOperation typename

auto multiplicative_inverse(double a) {
    return 1.0 / a;
}

// Section 7.1

bool odd(Integer n) { return bool(n & 0x1); }

auto half(Integer n) { return n >> 1; }

auto mult_acc4(int r, int n, int a) {
    while (true) {
        if (odd(n)) {
            r = r + a;
            if (n == 1) return r;
        }
        n = half(n);
        a = a + a;
    }
}

template <typename A, typename N>
auto multiply_accumulate0(A r, N n, A a) {
    while (true) {
        if (odd(n)) {
            r = r + a;
            if (n == 1) return r;
        }
        n = half(n);
        a = a + a;
    }
}

// Section 7.3

template <NoncommutativeAdditiveSemigroup A>
auto multiply_accumulate(A r, auto n, A a) {
    while (true) {
        if (odd(n)) {
            r = r + a;
            if (n == 1) return r;
        }
        n = half(n);
        a = a + a;
    }
}


template <NoncommutativeAdditiveSemigroup A>
auto multiply_accumulate_semigroup(A r, Integer n, A a) {
    // precondition(n >= 0);
    if (n == 0) return r;
    while (true) {
        if (odd(n)) {
            r = r + a;
            if (n == 1) return r;
        }
        n = half(n);
        a = a + a;
    }
}

auto multiply_semigroup(Integer n, NoncommutativeAdditiveSemigroup a) {
    // precondition(n > 0);
    while (!odd(n)) {
        a = a + a;
        n = half(n);
    }
    if (n == 1) return a;
    return multiply_accumulate_semigroup(a, half(n - 1), a + a);
}


// Section 7.4

auto multiply_monoid(Integer n, NoncommutativeAdditiveMonoid a) {
    // precondition(n >= 0);
    if (n == 0) return decltype(a){0};
    return multiply_semigroup(n, a);
}

auto multiply_group(Integer n, NoncommutativeAdditiveGroup a) {
    if (n < 0) {
        n = -n;
        a = -a;
    }
    return multiply_monoid(n, a);
}

// Section 7.5

template <MultiplicativeSemigroup A>
auto power_accumulate_semigroup(A r, A a, Integer n) {
    // precondition(n >= 0);
    if (n == 0) return r;
    while (true) {
        if (odd(n)) {
            r = r * a;
            if (n == 1) return r;
        }
        n = half(n);
        a = a * a;
    }
}

auto power_semigroup(MultiplicativeSemigroup a, Integer n) {
    // precondition(n > 0);
    while (!odd(n)) {
        a = a * a;
        n = half(n);
    }
    if (n == 1) return a;
    return power_accumulate_semigroup(a, a * a, half(n - 1));
}

auto power_monoid(MultiplicativeMonoid a, Integer n) {
    // precondition(n >= 0);
    if (n == 0) return decltype(a){1};
    return power_semigroup(a, n);
}

auto multiplicative_inverse(MultiplicativeGroup a) {
    return decltype(a){1} / a;
}

auto power_group(MultiplicativeGroup a, Integer n) {
    if (n < 0) {
        n = -n;
        a = multiplicative_inverse(a);
    }
    return power_monoid(a, n);
}

// Section 7.6

template <SemigroupOperation Op>
auto power_accumulate_semigroup(Regular r, Regular a, Integer n, Op op)
    //requires Same<Domain<decltype(op)>, decltype(a)>()
{
    // precondition(n >= 0);
    if (n == 0) return r;
    while (true) {
        if (odd(n)) {
            r = op(r, a);
            if (n == 1) return r;
        }
        n = half(n);
        a = op(a, a);
    }
}

template <SemigroupOperation Op>
auto power_semigroup(Regular a, Integer n, Op op)
    //requires Same<Domain<decltype(op)>, decltype(a)>()
{
    // precondition(n > 0);
    while (!odd(n)) {
        a = op(a, a);
        n = half(n);
    }
    if (n == 1) return a;
    return power_accumulate_semigroup(a, op(a, a), half(n - 1), op);
}

template <NoncommutativeAdditiveMonoid T>
auto identity_element(std::plus<T>) {
    return T{0};
}

template <MultiplicativeMonoid T>
auto identity_element(std::multiplies<T>) {
    return T{1};
}

template <MonoidOperation Op>
auto power_monoid(Regular a, Integer n, Op op)
    //requires Same<Domain<decltype(op)>, decltype(a)>()
{
    // precondition(n >= 0);
    if (n == 0) return identity_element(op);
    return power_semigroup(a, n, op);
}

template <AdditiveGroup T>
auto inverse_operation(std::plus<T>) {
    return std::negate<T>();
}

template <MultiplicativeGroup T>
struct reciprocal {
    auto operator()(const T& x) const {
        return T{1} / x;
    }
};

template <MultiplicativeGroup T>
auto inverse_operation(std::multiplies<T>) {
    return reciprocal<T>();
}

template <GroupOperation Op>
auto power_group(Regular a, Integer n, Op op)
    //requires(Domain<Op, A>)
{
    if (n < 0) {
        n = -n;
        a = inverse_operation(op)(a);
    }
    return power_monoid(a, n, op);
}


// Section 7.7

auto fib0(int n) {
    if (n == 0) return 0;
    if (n == 1) return 1;
    return fib0(n - 1) + fib0(n - 2);
}

auto fibonacci_iterative(int n) {
    if (n == 0) return 0;
    auto v = std::make_pair(0, 1);
    for (auto i = 1; i < n; ++i) {
        v = {v.second, v.first + v.second};
    }
    return v.second;
}
