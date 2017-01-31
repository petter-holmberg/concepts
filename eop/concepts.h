// concepts.h

// Copyright (c) 2017 Petter Holmberg
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.


// Concepts from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_CONCEPTS
#define EOP_CONCEPTS

#include <type_traits>

namespace experimental {

// For types X and Y, Same<X, Y> is true iff X and Y
// denote exactly the same type after elimination of aliases.
template <class T, class U>
concept bool Same() {
    return std::is_same<T, U>::value;
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

namespace {

template <class T, class ...Args>
concept bool __ConstructibleObject = // exposition only
    Destructible<T>() && requires (Args&& ...args) {
        T{std::forward<Args>(args)...}; // not required to be equality preserving
        new T{std::forward<Args>(args)...}; // not required to be equality preserving
    };

template <class T, class ...Args>
concept bool __BindableReference = // exposition only
    std::is_reference<T>::value && requires (Args&& ...args) {
        T(std::forward<Args>(args)...);
    };

} // namespace

template <class T, class ...Args>
concept bool Constructible() {
    return __ConstructibleObject<T, Args...> || __BindableReference<T, Args...>;
}

// For types X and Y, ConvertibleTo<X, Y> is true iff X can be implicitly converted to Y.
template <class T, class U>
concept bool ConvertibleTo() {
    return std::is_convertible<T, U>::value;
}

template <class T>
concept bool MoveConstructible() {
    return Constructible<T, std::remove_cv_t<T>&&>()
        && ConvertibleTo<std::remove_cv_t<T>&&, T>();
}

template <class T>
concept bool CopyConstructible() {
    return MoveConstructible<T>()
        && Constructible<T, const std::remove_cv_t<T>&>()
        && ConvertibleTo<std::remove_cv_t<T>&, T>()
        && ConvertibleTo<const std::remove_cv_t<T>&, T>()
        && ConvertibleTo<const std::remove_cv_t<T>&&, T>();
}

// For types X and Y, Common<X, Y> is true iff X and Y can both be
// unambiguously converted to a common type Z.
template <class T, class U>
concept bool Common() {
    return requires (T t, U u) {
        typename std::common_type_t<T, U>;
        typename std::common_type_t<U, T>;
        requires Same<std::common_type_t<U, T>, std::common_type_t<T, U>>();
        std::common_type_t<T, U>(std::forward<T>(t));
        std::common_type_t<T, U>(std::forward<U>(u));
        // axiom (T t1, T t2, U u1, U u2) {
        //     using C = std::common_type_t<T, U>;
        //     eq (t1, t2) <=> eq(C{t1}, C{t2});
        //     eq (u1, u2) <=> eq(C{u1}, C{u2});
        // }
    };
}

template <class T, class U>
concept bool Assignable() {
    return Common<T, U>()
        ///&& requires(T&& a, U&& b) {
        ///    { std::forward<T>(a) = std::forward<U>(b) } -> Same<T&>;
        ;
}

template <class T>
concept bool Swappable() {
    return requires(T&& a, T&& b) {
        std::swap(std::forward<T>(a), std::forward<T>(b));
    };
}

template <class T, class U>
concept bool Swappable() {
    return Swappable<T>()
        && Swappable<U>()
        && Common<T, U>()
        && requires(T&& t, U&& u) {
            std::swap(std::forward<T>(t), std::forward<U>(u));
            std::swap(std::forward<U>(u), std::forward<T>(t));
        };
}

template <class T>
concept bool Movable() {
    return MoveConstructible<T>()
        && Assignable<T&, T&&>()
        && Swappable<T&>();
    // axiom move_semantics {
    //     eq(a, b) => eq(T{std::move(a)}, b);
    //     eq(b, c) => eq(a = std::move(b), c);
    // }
}

template <class F, class ...Args>
concept bool Callable() {
    return CopyConstructible<F>()
        && requires (F f, Args&&...args) {
            invoke(f, std::forward<Args>(args)...); // Not required to be equality preserving.
        };
}

template <class F, class ...Args>
concept bool RegularCallable() {
    return Callable<F, Args...>();
    // axiom (F f, Args... args) {
    //     equality_preserving(f(args...));
    // }
}

template <class Op, class T>
concept bool BinaryOperation() {
    return RegularCallable<Op, T, T>() && ConvertibleTo<std::result_of_t<Op(T, T)>, T>();
}

template <class T>
concept bool Copyable() {
    return CopyConstructible<T>()
        && Movable<T>()
        && Assignable<T&, const T&>();
    // axiom copy_semantics {
    //     eq(T{a}, a);
    //     eq(a = b, b);
    // }
}

template <class T>
concept bool DefaultConstructible() {
    return Constructible<T>()
        && requires (const size_t n) {
            new T[n]{}; // Not required to be equality preserving.
        };
}

template <class T>
concept bool Semiregular() {
    return Copyable<T>() && DefaultConstructible<T>();
}

template <class B>
concept bool Boolean() {
//    return MoveConstructible<B>(); // TODO: Fails for bool, why?
    return requires(const B b1, const B b2, const bool a) {
            bool(b1);
            { b1 } -> bool;
            bool(!b1);
            { !b1 } -> bool;
            { b1 && b2 } -> Same<bool>;
            { b1 && a } -> Same<bool>;
            { a && b1 } -> Same<bool>;
            { b1 || b2 } -> Same<bool>;
            { b1 || a } -> Same<bool>;
            { a || b1 } -> Same<bool>;
            { b1 == b2 } -> bool;
            { b1 != b2 } -> bool;
            { b1 == a } -> bool;
            { a == b1 } -> bool;
            { b1 != a } -> bool;
            { a != b1 } -> bool;
        };
}

template <class T, class U>
concept bool WeaklyEqualityComparable() {
    return requires(const T t, const U u) {
        { t == u } -> Boolean;
        { u == t } -> Boolean;
        { t != u } -> Boolean;
        { u != t } -> Boolean;
    };
    // axiom { t == u <=> eq(t, u); }
    // axiom {
    //    t == t;
    //    t == u => u == t;
    //    t == u && u == c => t == c;
    // }
    // axiom { t != u <=> !(t == u); }
}

template <class T>
concept bool EqualityComparable() {
    return WeaklyEqualityComparable<T, T>();
}

template <class T>
concept bool Regular() {
    return Semiregular<T>() && EqualityComparable<T>();
}

template <class T>
concept bool StrictTotallyOrdered() {
    return EqualityComparable<T>()
        && requires (const T a, const T b) {
            { a < b } -> Boolean;
            { a > b } -> Boolean;
            { a <= b } -> Boolean;
            { a >= b } -> Boolean;
        };
}

} // namespace experimental

// EoP concepts

// For types X and Y, Same<X, Y> is true iff X and Y
// denote exactly the same type after elimination of aliases.
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

// Chapter 1: Foundations

template <class T, class... Args>
concept bool Regular() {
    return DefaultConstructible<T>()
        && Destructible<T>();
}

template <typename F, typename...Args>
concept bool FunctionalProcedure() {
    return true;
}

template <typename F>
concept bool UnaryFunction() {
    return FunctionalProcedure<F>()
        && Arity<F> == 1;
        // && Domain : UnaryFunction -> Regular
        //     F -> InputType(F, 0)
}

template <typename F>
concept bool HomogeneousFunction() {
    return FunctionalProcedure<F>()
        && Arity<F> > 0;
        // && Regular<T>() // Domain : UnaryFunction -> Regular
        // && ConvertibleTo<std::result_of_t<F(T)>, T>(); // f -> InputType(F, 0)
}

// Chapter 2: Transformations and Their Orbits

template <typename P>
concept bool Predicate() {
    return FunctionalProcedure<P>();
        // Codomain(P) = bool // && std::is_same<Codomain(P), bool>::value;
}

template <typename P>
concept bool HomogeneousPredicate() {
    return Predicate<P>()
        && HomogeneousFunction<P>();
}

template <typename P>
concept bool UnaryPredicate() {
    return Predicate<P>()
        && UnaryFunction<P>();
}

template <typename Op>
concept bool Operation() {
    return HomogeneousFunction<Op>();
        // Codomain(Op) = Domain(Op) // && std::is_same<Codomain(Op), Domain(Op)>::value;
}

template <typename F>
concept bool Transformation() {
    return Operation<F>()
        && UnaryFunction<F>();
        // DistanceType : Transformation -> Integer;
}

// Chapter 3: Associative Operations

template <typename Op>
concept bool BinaryOperation() {
    return Operation<Op>()
        && Arity<Op> == 2;
}

template <typename I>
concept bool Integer() {
    //return std::is_integral<I>::value &&
    return requires (I i) {
        { successor(i) } -> I
            // n -> n + 1
        { predecessor(i) } -> I
            // n -> n - 1
        { twice(i) } -> I
            // n -> n + n
        { half_nonnegative(i) } -> I
            // n -> floor(n / 2), where n >= 0
        { binary_scale_down_nonnegative(i, i) } -> I
            // (n, k) -> floor(n / 2^k), where n, k >= 0
        { binary_scale_up_nonnegative(i, i) } -> I
            // (n, k) -> 2^k * n, where n, k >= 0
        { positive(i) } -> bool
            // n -> n > 0
        { negative(i) } -> bool
            // n -> n < 0
        { zero(i) } -> bool
            // n -> n = 0
        { one(i) } -> bool
            // n -> n = 1
        { even(i) } -> bool
            // n -> (n mod 2) = 0
        { odd(i) } -> bool
            // n -> (n mod 2) != 0
    };
}

// Chapter 4: Linear Orderings

template <typename Op>
concept bool Relation() {
    return HomogeneousPredicate<Op>()
        && Arity<Op> == 2;
}

template <typename T>
concept bool TotallyOrdered() {
    return Regular<T>();
        // <: T * T -> bool
        // total_ordering(<)
}

// Chapter 5: Ordered Algebraic Structures

template <typename T>
concept bool AdditiveSemigroup() {
    return Regular<T>()
        && requires (const T& a, const T& b) {
            { a + b } -> T
        };
        // associative(+)
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
concept bool AdditiveMonoid() {
    return AdditiveSemigroup<T>()
        && requires (const T& a) {
            { zero(a) } -> T
            // identity_element(0, +)
        };
}

template <typename T>
concept bool MultiplicativeMonoid() {
    return MultiplicativeSemigroup<T>()
        && requires (const T& a) {
            { one(a) } -> T
            // identity_element(1, *)
        };
}

template <typename T>
concept bool AdditiveGroup() {
    return AdditiveMonoid<T>()
        && requires (const T& a, const T& b) {
            { -a } -> T
            // inverse_operation(unary -, 0, +)
            { a - b } -> T
                // (a, b) -> a + (-b)
        };
}

template <typename T>
concept bool MultiplicativeGroup() {
    return MultiplicativeMonoid<T>()
        && requires (const T& a, const T& b) {
            { multiplicative_inverse(a) } -> T
            // inverse_operation(multiplicative_inverse, 1, *)
            { a / b } -> T
                // (a, b) -> a * multiplicative_inverse(b)
        };
}

template <typename T>
concept bool Semiring() {
    return AdditiveMonoid<T>()
        && MultiplicativeMonoid<T>();
        // 0 != 1
        // all(a) in T : 0 * a == a * 0 == 0
        // all(a, b, c) in T
        //     a * (b + c) == a * b + a * c
        //     (b + c) * a == b * a + c * a
}

template <typename T>
concept bool CommutativeSemiring() {
    return Semiring<T>();
        // commutative(*)
}

template <typename T>
concept bool Ring() {
    return AdditiveGroup<T>()
        && Semiring<T>();
}

template <typename T>
concept bool CommutativeRing() {
    return AdditiveGroup<T>()
        && CommutativeSemiring<T>();
}

template <typename T, typename S>
concept bool Semimodule() {
    return AdditiveMonoid<T>()
        && CommutativeSemiring<T>()
        && requires (const S& a, const T& b) {
            { a * b } -> T
            // all(alfa, beta) in S and all(a, b in T)
            //     alfa * (beta * a) == (alfa * beta) * a
            //     (alfa + beta) * a == alfa * a + beta * a
            //     alfa * (a + b) == alfa * a + alfa * b
            //     1 * a == a
        };
}

template <typename T, typename S>
concept bool Module() {
    return Semimodule<T, S>()
        && AdditiveGroup<T>()
        && Ring<S>();
}

template <typename T>
concept bool OrderedAdditiveSemigroup() {
    return AdditiveSemigroup<T>()
        && TotallyOrdered<T>();
        // all(a, b, c) in T: a < b => a + c > b + c
}

template <typename T>
concept bool OrderedAdditiveMonoid() {
    return OrderedAdditiveSemigroup<T>()
        && AdditiveMonoid<T>();
}

template <typename T>
concept bool OrderedAdditiveGroup() {
    return OrderedAdditiveMonoid<T>()
        && AdditiveGroup<T>();
}

template <typename T>
concept bool CancellableMonoid() {
    return OrderedAdditiveMonoid<T>()
        && requires (const T& a, const T& b) {
            { a - b } -> T
            // all(a, b) in T : b <= a => a - b is defined and (a - b) + b == a
        };
}

template <typename T>
concept bool ArchimedeanMonoid() {
    return CancellableMonoid<T>();
        // all(a, b) in T : (a >= 0 and b > 0) => slow_remainder(a, b) terminates
        // QuotientType : ArchimedeanMonoid -> Integer
}

template <typename T>
concept bool HalvableMonoid() {
    return ArchimedeanMonoid<T>()
        && requires (const T& a) {
            { half(a) } -> T
            // all(a, b) in T : (b > 0 and a == b + b) => half(a) == b
        };
}

template <typename T>
concept bool EuclideanMonoid() {
    return ArchimedeanMonoid<T>();
        // all(a, b) in T : (a > 0 and b > 0) => subtractive_gcd_nonzero(a, b) terminates
}

template <typename T>
concept bool EuclideanSemiring() {
    return CommutativeSemiring<T>();
        // NormType : EucledianSemiring -> Integer
        // w : T -> NormType(T)
        // all(a) in T : w(a) >= 0
        // all(a) in T : w(a) == 0 <=> a == 0
        // all(a, b) in T : b != 0 => w(a * b) >= w(a)
        // remainder : T * T -> T
        // quotient : T * T -> T
        // all(a, b) in T : b != 0 => a == quotient(a, b) * b + remainder(a, b)
        // all(a, b) in T : b != 0 => w(remainder(a, b)) < w(b)
}

template <typename T, typename S>
concept bool EuclideanSemimodule() {
    return Semimodule<T, S>();
        // && requires (T& a, T& b) {
        //     { remainder(a, b) } -> T
        //     { quotient(a, b) } -> T
        //     all(a, b) in T : b != 0 => a = quotient(a, b) * b + remainder(a, b)
        //     all(a, b) in T : (a != 0 or b != 0) => gcd(a, b) terminates
        // };
}

template <typename T>
concept bool ArchimedeanGroup() {
    return ArchimedeanMonoid<T>()
        && AdditiveGroup<T>();
}

template <typename T>
concept bool DiscreteArchimedeanSemiring() {
    return CommutativeSemiring<T>()
        && ArchimedeanMonoid<T>();
        // all(a, b, c) in T : a < b and 0 < c => a * c < b * c
        // not(exists(a) in T) : 0 < a < 1
}

template <typename T>
concept bool NonnegativeDiscreteArchimedeanSemiring() {
    return DiscreteArchimedeanSemiring<T>();
        // all(a in T) : 0 <= a
}

template <typename T>
concept bool DiscreteArchimedeanRing() {
    return DiscreteArchimedeanSemiring<T>()
        && AdditiveGroup<T>();
}

// Chapter 6: Iterators

template <typename T>
concept bool Readable() {
    return Regular<T>()
        && Regular<ValueType<T>>()
        && requires (T a) {
            { source(a) } -> ValueType<T>
        };
}

template <typename T>
concept bool Iterator() {
    return Regular<T>()
        // DistanceType : Iterator -> Integer
        && requires (T a) {
            { successor(a) } -> T
            // successor is not necessarily regular
        };
}

template <typename T>
concept bool ForwardIterator() {
    return Iterator<T>();
        // regular_unary_function(successor)
}

template <typename T>
concept bool IndexedIterator() {
    return ForwardIterator<T>()
        && requires(T a, DistanceType<T> b) {
            { a + b } -> T
            // { a - c } -> T // - : T * T -> DistanceType(T)
        };
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
        && TotallyOrdered<T>()
        && requires(T a, DistanceType<T> b) {
            // all(i, j) in T : i < j <=> i < j
            // DifferenceType : RandomAccessIterator -> Integer
            { a + b } -> T
            // - : T * DifferenceType(T) -> T
            // - : T * T -> DifferenceType(T)
            // < takes constant time
            // - between an iterator and an integer takes constant time
        };
}

// Chapter 7: Coordinate structures

template <typename T>
concept bool BifurcateCoordinate() {
    return Regular<T>()
        && Integer<WeightType<T>>()
        && requires(T a) {
            { empty(a) } -> bool
            { has_left_successor(a) } -> bool
            { has_right_successor(a) } -> bool
            { left_successor(a) } -> T
            { right_successor(a) } -> T
            // all(i, j) in T : (left_successor(i) == j or right_successor(i) == j) >= not(empty(i))
        };
}

template <typename T>
concept bool BidirectionalBifurcateCoordinate() {
    return BifurcateCoordinate<T>()
        && requires(T a) {
            { has_predecessor(a) } -> bool
            // all(i) in T : not(empty(i)) => has_predecessor(i) is defined
            { predecessor(a) } -> T
            // all(i) in T : has_left_successor(i) => predecessor(left_successor(i)) is defined and equals i
            // all(i) in T : has_right_successor(i) => predecessor(right_successor(i)) is defined and equals i
            // all(i) in T : has_predecessor(i) => is_left_successor(i) or is_right_successor(i)
        };
}

template <typename F>
concept bool Comparator3Way() {
    return HomogeneousFunction<F>()
        && Arity<F> == 2;
        //  /\ Codomain(F) = int
}

template <typename F>
concept bool LinkedForwardIterator() {
    return true;
}

template <typename F>
concept bool LinkedBidirectionalIterator() {
    return true;
}

template <typename F>
concept bool UnaryPseudoPredicate() {
    return true;
}

template <typename F>
concept bool PseudoRelation() {
    return true;
}


// Chapter 8: Coordinates with Mutable Successors

template <typename S>
concept bool ForwardLinker() {
    return ForwardIterator<IteratorType<S>>();
    // Let I = IteratorType<S> in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if successor(i) is defined,
    //         then s(i, j) establishes successor(i) == j
}

template <typename S>
concept bool BackwardLinker() {
    return BidirectionalIterator<IteratorType<S>>();
    // Let I = IteratorType<S> in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if prececessor(i) is defined,
    //         then s(i, j) establishes i == predecessor(j)
}

template <typename S>
concept bool BidirectionalLinker() {
    return ForwardLinker<S>()
        && BackwardLinker<S>();
}

template <typename T>
concept bool LinkedBifurcateCoordinate() {
    return BifurcateCoordinate<T>()
        && requires(T a) {
            { set_left_successor(a, a) } -> void
            //     (i, j) -> establishes left_successor(i) == j
            { set_right_successor(a, a) } -> void
            //     (i, j) -> establishes right_successor(i) == j
        };
}

template <typename T>
concept bool EmptyLinkedBifurcateCoordinate() {
    return LinkedBifurcateCoordinate<T>()
        && requires(T a) {
            empty(a);
            // empty(T()) (In other words, empty is true on the default constructed value and possibly on other values as well)
            // not(empty(i)) => left_successor(i) and right_successor(i) are defined
            // not(empty(i)) => (not(has_left_successor(i) <=> empty(left_successor(i))))
            // not(empty(i)) => (has_right_successor(i) <=> empty(right_successor(i))))
        };
}

// Chapter 9: Copying

template <typename T>
concept bool Writable() {
    return Regular<ValueType<T>>()
        && requires(T x) {
            sink(x);
            // all(x in T) : (all(v) in ValueType<T>) : sink(x) <- v is a well-formed statement
    };
}

template <typename T>
concept bool Mutable() {
    return Readable<T>()
        && Writable<T>()
        && requires(T x) {
            sink(x);
            source(x);
            // all(x) in T : sink(x) is defined <=> source(x) is defined
            // all(x) in T : sink(x) is defined => aliased(x, x)
            { deref(x) } -> ValueType<T>&
            // all(x) in T : sink(x) is defined <=> deref(x) is defined
        };
}

// Chapter 12: Composite Objects

template <typename W>
concept bool Linearizable() {
    return Regular<W>()
        // IteratorType : Linearizable -> Integer
        && Regular<ValueType<W>>()
        //     W -> ValueType<IteratorType<W>>
        && Integer<SizeType<W>>()
        //     W -> DistanceType(IteratorType<W>)
        && requires(W x) {
            { begin(x) } -> IteratorType<W>
            { end(x) } -> IteratorType<W>
            // { size(x) } -> SizeType<W>
            //     x -> end(x) - begin(x)
            // { empty(x) } -> bool
            //     x -> begin(x) == end(x)
            // [] : W * SizeType<W> -> ValueType<W>&
            //     (w, i) -> deref(begin(w) + i)
        };
}

template <typename S>
concept bool Sequence() {
    return Linearizable<S>()
        && requires(S x) {
            begin(x);
            end(x);
            // all(s) in S : all(i) in [begin(s), end(s))) deref(i) is a part of s
            // = : S * S -> bool
            //     (s, s') -> lexicographical_equal(begin(s), end(s), begin(s'), end(s'))
            // < : S * S -> bool
            //     (s, s') -> lexicographical_less(begin(s), end(s), begin(s'), end(s'))
        };
}

template <typename S>
concept bool BinaryPredicate() {
    return true;
}

template <typename T>
concept bool Position() {
    return Linearizable<BaseType<T>>()
        && Iterator<IteratorType<T>>()
        && Regular<ValueType<T>>()
        //         T |- ValueType<IteratorType<T>>
        && Integer<SizeType<T>>()
        //         T |- SizeType<IteratorType<T>>
        && requires(T x) {
        { base(x) } -> BaseType<T>
        { current(x) } -> IteratorType<T>
        { begin(x) } -> IteratorType<T>
        //         x |- begin(base(x))
        { end(x) } -> IteratorType<T>
        //         x |- end(base(x))
    };
}

template <typename T>
concept bool DynamicSequence() {
    return Sequence<T>();
    //  /\ T supports insert and erase
}

template <typename T>
concept bool InsertPosition() {
    return Position<T>()
        && DynamicSequence<BaseType<T>>();
}

template <typename T>
concept bool ErasePosition() {
    return Position<T>()
        && DynamicSequence<BaseType<T>>();
}

template <typename T, typename U>
concept bool Constructible() {
    return true;
}

template <typename T, typename U>
concept bool Destroyable() {
    return true;
}

template <typename T>
concept bool TreeNodeConstructor() {
    return true;
}

template <typename T>
concept bool TreeNodeDeleter() {
    return true;
}

#endif // EOP_CONCEPTS
