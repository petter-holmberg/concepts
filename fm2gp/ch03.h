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
// ch03.h -- Functions from Chapter 3 of fM2GP.
// -------------------------------------------------------------------

#include <algorithm>

template<typename F>
struct distance_type;

template<>
struct distance_type<int>
{
    using type = unsigned int;
};

template<>
struct distance_type<long long>
{
    using type = unsigned long long;
};

template<typename T>
using DistanceType = typename distance_type<T>::type;

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
concept bool TotallyOrdered() {
    return Regular<T>();
        // <: T * T -> bool
        // total_ordering(<)
}

template <typename T>
concept bool Iterator() {
    return Regular<T>()
        // DistanceType : Iterator -> Integer
        && requires (T a) {
            { a++ } -> T // successor is not necessarily regular
        };
}
template <typename T>
concept bool ForwardIterator() {
    return Iterator<T>();
        // regular_unary_function(successor)
}

template <typename T>
concept bool IndexedIterator() {
    return ForwardIterator<T>();
        // && requires(T a, DistanceType<T> b) {
        //    { a + b } -> T
        //    // { a - c } -> T // - : T * T -> DistanceType(T)
        //};
        // + takes constant time
        // - takes constant time
}

template <typename T>
concept bool BidirectionalIterator() {
    return ForwardIterator<T>();
        // { predecessor(a) } -> T
        // predecessor takes constant time
        // all(i) in T : successor(i) is defined =>
        //     predecessor(successor(i)) is defined and equals i
        // all(i) in T : predecessor(i) is defined =>
        //     successor(predecessor(i)) is defined and equals i
}

template <typename T>
concept bool RandomAccessIterator() {
    return IndexedIterator<T>()
        && BidirectionalIterator<T>()
        && ForwardIterator<T>()
        && TotallyOrdered<T>();
        // && requires(T a, DistanceType<T> b) {
        //    // all(i, j) in T : i < j <=> i < j
        //    // DifferenceType : RandomAccessIterator -> Integer
        //    { a + b } -> T
        //    // - : T * DifferenceType(T) -> T
        //    // - : T * T -> DifferenceType(T)
        //    // < takes constant time
        //    // - between an iterator and an integer takes constant time
        // };
}

template <typename I>
concept bool Integer() {
    return std::is_integral<I>::value;
}

// Section 3.3

void mark_sieve(RandomAccessIterator first, RandomAccessIterator last, Integer factor) {
    // assert(first != last)
    *first = false;
    while (last - first > factor) {
        first = first + factor;
        *first = false;
    }
}

void sift0(RandomAccessIterator first, Integer n) {
    std::fill(first, first + n, true);
    using N = decltype(n);
    N i{0};
    N index_square{3};
    while (index_square < n) {
        // invariant: index_square = 2i^2 + 6i + 3
        if (first[i]) {     // if current candidate is prime
            mark_sieve(
                first + index_square,
                first + n,  // last
                i + i + 3); // factor
        }
        ++i;
        index_square = 2*i*(i + 3) + 3;
    }
}

void sift1(RandomAccessIterator first, Integer n) {
    auto last = first + n;
    std::fill(first, last, true);
    using N = decltype(n);
    N i{0};
    N index_square{3};
    N factor{3};
    while (index_square < n) {
        // invariant: index_square = 2i^2 + 6i + 3, factor = 2i + 3
        if (first[i]) mark_sieve(first + index_square, last, factor);
        ++i;
        factor = i + i + 3;
        index_square = 2*i*(i + 3) + 3;
    }
}

void sift(RandomAccessIterator first, Integer n) {
    auto last = first + n;
    std::fill(first, last, true);
    using N = decltype(n);
    N i{0};
    N index_square{3};
    N factor{3};
    while (index_square < n) {
        // invariant: index_square = 2i^2 + 6i + 3, factor = 2i + 3
        if (first[i]) mark_sieve(first + index_square, last, factor);
        ++i;
        index_square += factor;
        factor += N{2};
        index_square += factor;
    }
}

// Section 3.5

using line_segment = unsigned;

auto gcm(line_segment a, line_segment b) {
    if (a == b)   return a;
    if (b < a)    return gcm(a - b, b);
 /* if (a < b) */ return gcm(a, b - a);
}
