#pragma once

#include "concepts.hpp"

namespace eop {

// Chapter 1: Foundations

template <class T>
concept bool Regular() {
    return ::Regular<T>();
};

template <class F, class...Args>
concept bool FunctionalProcedure() {
    return ::RegularCallable<F, Args...>();
};

template <class F>
concept bool UnaryFunction() {
    return FunctionalProcedure<F>();
        // Arity(F) = 1
        // Domain : UnaryFunction -> Regular
        //     F -> InputType(F, 0)
};

template <class F>
concept bool HomogenousFunction() {
    return FunctionalProcedure<F>();
        // Arity(F) > 0
        // (All(i,j) in N : i,j < Arity(F)) => (InputType(F, i) == InputType(F, j))
        // Domain : HomogenousFunction -> Regular
        //     F -> InputType(F, 0)
};

// Chapter 2: Transformations and Their Orbits

template <class P>
concept bool Predicate() {
    return FunctionalProcedure<P>();
        // Codomain(P) == bool
};

template <class P>
concept bool HomogenousPredicate() {
    return Predicate<P>()
        && HomogenousFunction<P>();
};

template <class P>
concept bool UnaryPredicate() {
    return Predicate<P>()
        && UnaryFunction<P>();
};

template <class Op>
concept bool Operation() {
    return HomogenousFunction<Op>();
        // Codomain(Op) == Domain(Op);
};

template <class F>
concept bool Transformation() {
    return Operation<F>()
        && UnaryFunction<F>();
        // DistanceType : Transformation -> Integer
};

// Chapter 3: Associative Operations

template <class Op>
concept bool BinaryOperation() {
    return Operation<Op>();
        // Arity(Op) == 2
};

template <class I>
concept bool Integer() {
    return false;
    // successor: I -> I
    //     n -> n + 1
    // predecessor: I - I
    //     n -> n - 1
    // twice: I -> I
    //     n -> n + n
    // half_nonnegative: I -> I
    //     n -> floor(n / 2), wher n >= 0
    // binary_scale_down_nonnegative: I * I -> I
    //     (n, k) -> floor(n / 2^k), where n, k >= 0
    // binary_scale_up_nonnegative: I * I -> I
    //     (n, k) -> 2^k * n, where n, k >= 0
    // positive: I -> bool
    //     n -> n > 0
    // negative: I -> bool
    //     n -> n < 0
    // zero: I -> bool
    //     n -> n = 0
    // one: I -> bool
    //     n -> n = 1
    // even: I -> bool
    //     n -> (n mod 2) = 0
    // odd: i -> bool
    //     n -> (n mod 2) != 0
};

// Chapter 4: Linear Orderings

template <class Op>
concept bool Relation() {
    return HomogenousPredicate<Op>();
    // Arity(Op) == 2
};

template <class T>
concept bool TotallyOrdered() {
    return Regular<T>();
        // <: T * T -> bool
        // total_ordering(<)
};

// Chapter 5: Ordered Algebraic Structures

template <class T>
concept bool AdditiveSemigroup() {
    return Regular<T>();
        // +: T * T -> T
};

template <class T>
concept bool MultiplicativeSemigroup() {
    return Regular<T>();
        // *: T * T -> T
        // associative(*)
};

template <class T>
concept bool AdditiveMonoid() {
    return AdditiveSemigroup<T>();
        // 0 in T
        // identity_element(0, +)
};

template <class T>
concept bool MultiplicativeMonoid() {
    return MultiplicativeSemigroup<T>();
        // 1 in T
        // identity_element(1, *)
};

template <class T>
concept bool AdditiveGroup() {
    return AdditiveMonoid<T>();
        // - : T -> T
        // inverse_operation(unary -, 0, +)
        // - : T * T -> T
        //     (a, b) -> a + (-b)
};

template <class T>
concept bool MultiplicativeGroup() {
    return MultiplicativeMonoid<T>();
        // multiplicative_inverse : T -> T
        // inverse_operation(multiplicative_inverse, 1, *)
        // / : T * T -> T
        //     (a, b) -> a * multiplicative_inverse(b)
};

template <class T>
concept bool Semiring() {
    return AdditiveMonoid<T>()
        && MultiplicativeMonoid<T>();
        // 0 != 1
        // all(a) in T : 0 * a == a * 0 == 0
        // all(a, b, c) in T
        //     a * (b + c) == a * b + a * c
        //     (b + c) * a == b * a + c * a
};

template <class T>
concept bool CommutativeSemiring() {
    return Semiring<T>();
        // commutative(*)
};

template <class T>
concept bool Ring() {
    return AdditiveGroup<T>()
        && Semiring<T>();
};

template <class T>
concept bool CommutativeRing() {
    return AdditiveGroup<T>()
        && CommutativeSemiring<T>();
};

template <class T, class S>
concept bool Semimodule() {
    return AdditiveMonoid<T>()
        && CommutativeSemiring<T>();
        // * : S * T -> T
        // all(alfa, beta) in S and all(a, b in T)
        //     alfa * (beta * a) == (alfa * beta) * a
        //     (alfa + beta) * a == alfa * a + beta * a
        //     alfa * (a + b) == alfa * a + alfa * b
        //     1 * a == a
};

template <class T, class S>
concept bool Module() {
    return Semimodule<T, S>()
        && AdditiveGroup<T>()
        && Ring<S>();
};

template <class T>
concept bool OrderedAdditiveSemigroup() {
    return AdditiveSemigroup<T>()
        && TotallyOrdered<T>();
        // all(a, b, c) in T: a < b => a + c > b + c
};

template <class T>
concept bool OrderedAdditiveMonoid() {
    return OrderedAdditiveSemigroup<T>()
        && AdditiveMonoid<T>();
};

template <class T>
concept bool OrderedAdditiveGroup() {
    return OrderedAdditiveMonoid<T>()
        && AdditiveGroup<T>();
};

template <class T>
concept bool CancellableMonoid() {
    return OrderedAdditiveMonoid<T>();
        // - : T * T -> T
        // all(a, b) in T : b <= a => a - b is defined and (a - b) + b == a
};

template <class T>
concept bool ArchimedianMonoid() {
    return CancellableMonoid<T>();
        // all(a, b) in T : (a >= 0 and b > 0) => slow_remainder(a, b) terminates
        // QuotientType : ArchimedianMonoid -> Integer
};

template <class T>
concept bool HalvableMonoid() {
    return ArchimedianMonoid<T>();
        // half : T -> T
        // all(a, b) in T : (b > 0 and a == b + b) => half(a) == b
};

template <class T>
concept bool EuclideanMonoid() {
    return ArchimedianMonoid<T>();
        // all(a, b) in T : (a > 0 and b > 0) => subtractive_gcd_nonzero(a, b) terminates
};

template <class T>
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
};

template <class T, class S>
concept bool EuclideanSemimodule() {
    return Semimodule<T, S>();
        // remainder : T * T -> T
        // quotient : T * T -> S
        // all(a, b) in T : b != 0 => a = quotient(a, b) * b + remainder(a, b)
        // all(a, b) in T : (a != 0 or b != 0) => gcd(a, b) terminates
};

template <class T>
concept bool ArchimedianGroup() {
    return ArchimedianMonoid<T>()
        && AdditiveGroup<T>();
};

template <class T>
concept bool DiscreteArchimedianSemiring() {
    return CommutativeSemiring<T>()
        && ArchimedianMonoid<T>();
        // all(a, b, c) in T : a < b and 0 < c => a * c < b * c
        // not(exists(a) in T) : 0 < a < 1
};

template <class T>
concept bool NonnegativeDiscreteArchimedianSemiring() {
    return DiscreteArchimedianSemiring<T>();
        // all(a in T) : 0 <= a
};

template <class T>
concept bool DiscreteArchimedianRing() {
    return DiscreteArchimedianSemiring<T>()
        && AdditiveGroup<T>();
};

// Chapter 6: Iterators

template <class T>
concept bool Readable() {
    return Regular<T>();
        // ValueType : Readable -> Regular
        // source : T -> ValueType(T)
};

template <class T>
concept bool Iterator() {
    return Regular<T>();
        // DistanceType : Iterator -> Integer
        // successor : T -> T
        // successor is not necessarily regular
};

template <class T>
concept bool ForwardIterator() {
    return Iterator<T>();
        // regular_unary_function(successor)
};

template <class T>
concept bool IndexedIterator() {
    return ForwardIterator<T>();
        // + : T * DistanceType(T) -> T
        // - : T * T -> DistanceType(T)
        // + takes constant time
        // - takes constant time
};

template <class T>
concept bool BidirectionalIterator() {
    return ForwardIterator<T>();
        // predecessor : T -> T
        // predecessor takes constant time
        // all(i) in T : successor(i) is defined =>
        //     predecessor(successor(i)) is defined and equals i
        // all(i) in T : predecessor(i) is defined =>
        //     successor(predecessor(i)) is defined and equals i
};

template <class T>
concept bool RandomAccessIterator() {
    return IndexedIterator<T>()
        && BidirectionalIterator<T>()
        && ForwardIterator<T>()
        && TotallyOrdered<T>();
        // all(i, j) in T : i < j <=> i < j
        // DifferenceType : RandomAccessIterator -> Integer
        // + : T * DifferenceType(T) -> T
        // - : T * DifferenceType(T) -> T
        // - : T * T -> DifferenceType(T)
        // < takes constant time
        // - between an iterator and an integer takes constant time
};

// Chapter 7: Coordinate structures

template <class T>
concept bool BifurcateCoordinate() {
    return Regular<T>();
        // WeightType : BifurcateCoordinate -> Integer
        // empty : T -> bool
        // has_left_successor : T -> bool
        // has_right_successor : T -> bool
        // left_successor : T -> T
        // right_successor : T -> T
        // all(i, j) in T : (left_successor(i) == j or right_successor(i) == j) >= not(empty(i))
};

template <class T>
concept bool BidirectionalBifurcateCoordinate() {
    return BifurcateCoordinate<T>();
        // has_predecessor : T -> bool
        // all(i) in T : not(empty(i)) => has_predecessor(i) is defined
        // predecessor : T -> T
        // all(i) in T : has_left_successor(i) => predecessor(left_successor(i)) is defined and equals i
        // all(i) in T : has_right_successor(i) => predecessor(right_successor(i)) is defined and equals i
        // all(i) in T : has_predecessor(i) => is_left_successor(i) or is_right_successor(i)
};

// Chapter 8: Coordinates with Mutable Successors

template <class S>
concept bool ForwardLinker() {
    return true;
    // IteratorType : ForwardLinker -> ForwardIterator
    // Let I = IteratorType(S) in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if successor(i) is defined,
    //         then s(i, j) establishes successor(i) == j
};

template <class S>
concept bool BackwardLinker() {
    return true;
    // IteratorType : BackwardLinker -> BidirectionalIterator
    // Let I = IteratorType(S) in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if prececessor(i) is defined,
    //         then s(i, j) establishes i == predecessor(j)
};

template <class S>
concept bool BidirectionalLinker() {
    return ForwardLinker<S>()
        && BackwardLinker<S>();
};

template <class T>
concept bool LinkedBifurcateCoordinate() {
    return BifurcateCoordinate<T>();
        // set_left_successor : T * T -> void
        //     (i, j) -> establishes left_successor(i) == j
        // set_right_successor : T * T -> void
        //     (i, j) -> establishes right_successor(i) == j
};

template <class T>
concept bool EmptyLinkedBifurcateCoordinate() {
    return LinkedBifurcateCoordinate<T>();
        // empty(T())
        // not(empty(i)) => left_successor(i) and right_successor(i) are defined
        // not(empty(i)) => (not(has_left_successor(i) <=> empty(left_successor(i))))
        // not(empty(i)) => (has_right_successor(i) <=> empty(right_successor(i))))
};

// Chapter 9: Copying

template <class T>
concept bool Writable() {
    return true;
        // ValueType : Writable -> Regulars
        // all(x in T) : (all(v) in ValueType(T)) : sink(x) <- v is a well-formed statement
};

template <class T>
concept bool Mutable() {
    return Readable<T>()
        && Writable<T>();
        // all(x) in T : sink(x) is defined <=> source(x) is defined
        // all(x) in T : sink(x) is defined => aliased(x, x)
        // deref : t -> ValueType(T)&
        // all(x) in T : sink(x) is defined <=> deref(x) is defined
};

// Chapter 12: Composite Objects

template <class W>
concept bool Linearizable() {
    return Regular<W>();
    // IteratorType : Linearizable -> Integer
    // ValueType : Linearizabe -> Regular
    //     W -> ValueType(IteratorType(W))
    // SizeType : Linearizable -> Integer
    //     W -> DistanceType(IteratorType(W))
    // begin : W -> IteratorType(W)
    // end : W -> IteratorType(W)
    // size : W -> SizeType(W)
    //     x -> end(x) - begin(x)
    // empty : W -> bool
    //     x -> begin(x) == end(x)
    // [] : W * SizeType(W) -> ValueType(W)&
    //     (w, i) -> deref(begin(w) + i)
};

template <class S>
concept bool Sequence() {
    return Linearizable<S>();
        // all(s) in S : all(i) in [begin(s), end(s))) deref(i) is a part of s
        // = : S * S -> bool
        //     (s, s') -> lexicographical_equal(begin(s), end(s), begin(s'), end(s'))
        // < : S * S -> bool
        //     (s, s') -> lexicographical_less(begin(s), end(s), begin(s'), end(s'))
};

} // namespace eop

