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

#include <functional>
#include <type_traits>

#define concept concept bool

/*template <typename T>
    //requires TotallyOrdered<T>
struct less
{
    bool operator()(const T& x, const T& y)
    {
        return x < y;
    }
};
*/

// For types X and Y, Same<X, Y> is true iff X and Y
// denote exactly the same type after elimination of aliases.
template <typename T, typename U>
concept Same = std::is_same<T, U>::value;

template <typename T, typename U>
concept Same_remove_cv = std::is_same<typename std::remove_cv<T>::type, typename std::remove_cv<U>::type>::value;

template <typename T>
concept Equality_comparable =
    requires (const T& x, const T& y) {
        { x == y } -> bool;
        { x != y } -> bool;
        // axiom equivalence_relation {
        //     x == x;
        //     x == y => y == x;
        //     x == y && y == z => x == z;
        // }
        // axiom equality {
        //     x == y <=> eq(x, y);
        // }
        // axiom complement {
        //     x != y <=> !(y == x);
        // }
        // complexity {
        //     O(areaof(min(areaof(x), areaof(y))));
        // }
    };

template <typename T, typename U>
concept Equality_comparable_with =
    requires (const T& x, const U& y) {
        { x == y } -> bool;
        { x != y } -> bool;
        { y == x } -> bool;
        { y != x } -> bool;
    };

template <typename T, typename U>
concept Assignable =
    requires (T x, U&& y) {
        { x = std::forward<U>(y) } -> T&;
        // axiom copy_semantics {
        //     is_lvalue_reference<decltype(y)> => eq(x = y, y);
        // }
        // axiom move_semantics {
        //     is_rvalue_reference<decltype(y)> => eq(x, y) => eq(x, z = std::move(y));
        // }
        // complexity {
        //     is_lvalue_reference<decltype(y)> => O(areaof(y));
        //     is_rvalue_reference<decltype(y)> => O(sizeof(y));
        // }
    };

template <typename T>
concept Equality_comparable = true;
/*    requires (const T& x, const T& y) {
        { x == y } -> bool;
        { x != y } -> bool;
        // axiom equivalence_relation {
        //     x == x;
        //     x == y => y == x;
        //     x == y && y == z => x == z;
        // }
        // axiom equality {
        //     x == y <=> eq(x, y);
        // }
        // axiom complement {
        //     x != y <=> !(y == x);
        // }
        // complexity {
        //     O(areaof(min(areaof(x), areaof(y))));
        // }
    };
*/

template <typename T, typename U>
concept Equality_comparable_with =
    requires (const T& x, const U& y) {
        { x == y } -> bool;
        { x != y } -> bool;
        { y == x } -> bool;
        { y != x } -> bool;
    };

template <typename T>
concept Destructible =
    std::is_nothrow_destructible<T>::value;
    // axiom end_of_object_lifetimes {}
    // complexity {
    //     O(areaof(x));
    // }

template <typename T, typename ...Args>
concept Constructible =
    Destructible<T> &&
    std::is_constructible<T, Args...>::value;

template <typename T>
concept Default_constructible = Constructible<T>;

template <typename T>
concept Move_constructible =
    std::is_convertible<T, T&&>::value &&
    Constructible<T, T&&>;
    // axiom move_semantics {
    //     eq(x, y) => eq(T{std::move(x)}, y);
    // }
    // complexity {
    //     O(sizeof(x));
    // }

template <typename T>
concept Copy_constructible =
    //Move_constructible<T> &&
    Constructible<T, const T&>;
    // axiom copy_semantics {
    //     eq(T{x}, y);
    // }
    // complexity {
    //     O(sizeof(y));
    // }

template <typename T>
concept Movable =
    std::is_object<T>::value &&
    Move_constructible<T> &&
    Assignable<T, T&&>;
    // axiom partially_formed {
    //     // std::move(x) not necessarily well-formed*
    //     T{std::move(x)} => x = std::move(y);
    //     T{std::move(x)} => ~x;
    //     y = std::move(x) => x = std::move(y);
    //     y = std::move(x) => ~x;
    // }

template <typename T>
concept Copyable = true;
    //Copy_constructible<T>;
    //Movable<T>;// &&
    //Copy_constructible<T>;// &&
    //Assignable<T, const T&>;
    // axiom partially_formed {
    //     // std::move(a) not necessarily well-formed
    //     T{std::move(a)} => a = b;
    //     b = std::move(a) = a = b;
    // }
/*
template <typename T>
concept Default_totally_ordered =
    Equality_comparable<T> &&
    requires (const T& x, const T& y) {
        { less<T>{}(x, y) } -> bool;
        // axiom total_ordering {
        //    std::less<T>{}(x, y) && std::less<T>{}(y, z) => std::less<T>{}(x, z);
        //    std::less<T>{}(x, y) || std::less<T>{}(y, x) || x == y;
        // }
        // complexity {
        //     O(areaof(x));
        // }
    };
*/
// Chapter 1: Foundations

template <typename T>
concept Regular =
    Equality_comparable<T> &&
    Default_constructible<T> &&
    Copyable<T>;
    // Default_totally_ordered<T>;
    // axiom partially_formed {
    //     // T x not necessarily well-formed
    //     T x => x = std::move(y);
    //     T x => x = y;
    //     T x => ~x;
    // }
    // complexity default_constructor {
    //     O(1);
    // }

template <typename T>
typename std::decay<T>::type decay_(T&&);

template <typename F>
inline decltype(auto) make_invokable(F&& fn) { return fn; }

template <typename P, typename ...Args>
concept Procedure =
    requires (P p, Args... args) {
        make_invokable(decay_(p))(args...);
    };

template <typename F, typename ...Args>
concept FunctionalProcedure = true;

template <typename F>
concept UnaryFunction = FunctionalProcedure<F> && Arity<F> == 1;
    // && Domain : UnaryFunction -> Regular
    //     F -> InputType(F, 0)

template <typename F>
concept HomogeneousFunction =
    FunctionalProcedure<F> && Arity<F> > 0;
        // && Regular<T> // Domain : UnaryFunction -> Regular
        // && ConvertibleTo<std::result_of_t<F(T)>, T>(); // f -> InputType(F, 0)

// Chapter 2: Transformations and Their Orbits

template <typename P>
concept Predicate = FunctionalProcedure<P>;
    // Codomain(P) = bool // && std::is_same<Codomain(P), bool>::value;

template <typename P>
concept HomogeneousPredicate = Predicate<P> && HomogeneousFunction<P>;

template <typename P>
concept UnaryPredicate = Predicate<P> && UnaryFunction<P>;

template <typename Op>
concept Operation = HomogeneousFunction<Op>;
    // Codomain(Op) = Domain(Op) // && std::is_same<Codomain(Op), Domain(Op)>::value;

template <typename F>
concept Transformation = Operation<F> && UnaryFunction<F>;
    // DistanceType : Transformation -> Integer;

// Chapter 3: Associative Operations

template <typename Op>
concept BinaryOperation = Operation<Op> && Arity<Op> == 2;

template <typename I>
concept Integer =
    //return std::is_integral<I>::value &&
    requires (I i) {
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

// Chapter 4: Linear Orderings

template <typename Op>
concept Relation = HomogeneousPredicate<Op> && Arity<Op> == 2;

template <typename T>
concept TotallyOrdered = Regular<T>;
    // <: T * T -> bool
    // total_ordering(<)

// Chapter 5: Ordered Algebraic Structures

template <typename T>
concept AdditiveSemigroup =
    Regular<T> &&
    requires (const T& a, const T& b) {
        { a + b } -> T
    };
    // associative(+)
    // commutative(+)

template <typename T>
concept MultiplicativeSemigroup =
    Regular<T> &&
    requires (const T& a, const T& b) {
        { a * b } -> T
    };
    // associative(*)

template <typename T>
concept AdditiveMonoid =
    AdditiveSemigroup<T> &&
    requires (const T& a) {
        { zero(a) } -> T
        // identity_element(0, +)
    };

template <typename T>
concept MultiplicativeMonoid =
    MultiplicativeSemigroup<T> &&
    requires (const T& a) {
        { one(a) } -> T
        // identity_element(1, *)
    };

template <typename T>
concept AdditiveGroup =
    AdditiveMonoid<T> &&
    requires (const T& a, const T& b) {
        { -a } -> T
        // inverse_operation(unary -, 0, +)
        { a - b } -> T
            // (a, b) -> a + (-b)
    };

template <typename T>
concept MultiplicativeGroup =
    MultiplicativeMonoid<T> &&
    requires (const T& a, const T& b) {
       { multiplicative_inverse(a) } -> T
        // inverse_operation(multiplicative_inverse, 1, *)
        { a / b } -> T
            // (a, b) -> a * multiplicative_inverse(b)
    };

template <typename T>
concept Semiring = AdditiveMonoid<T> && MultiplicativeMonoid<T>;
    // 0 != 1
    // all(a) in T : 0 * a == a * 0 == 0
    // all(a, b, c) in T
    //     a * (b + c) == a * b + a * c
    //     (b + c) * a == b * a + c * a

template <typename T>
concept CommutativeSemiring = Semiring<T>;
    // commutative(*)

template <typename T>
concept Ring = AdditiveGroup<T> && Semiring<T>;

template <typename T>
concept CommutativeRing = AdditiveGroup<T> && CommutativeSemiring<T>;

template <typename T, typename S>
concept Semimodule =
    AdditiveMonoid<T> &&
    CommutativeSemiring<T> &&
    requires (const S& a, const T& b) {
        { a * b } -> T
        // all(alfa, beta) in S and all(a, b in T)
        //     alfa * (beta * a) == (alfa * beta) * a
        //     (alfa + beta) * a == alfa * a + beta * a
        //     alfa * (a + b) == alfa * a + alfa * b
        //     1 * a == a
    };

template <typename T, typename S>
concept Module = Semimodule<T, S> && AdditiveGroup<T> && Ring<S>;

template <typename T>
concept OrderedAdditiveSemigroup = AdditiveSemigroup<T> && TotallyOrdered<T>;
    // all(a, b, c) in T: a < b => a + c > b + c

template <typename T>
concept OrderedAdditiveMonoid =
    OrderedAdditiveSemigroup<T> && AdditiveMonoid<T>;

template <typename T>
concept OrderedAdditiveGroup = OrderedAdditiveMonoid<T> && AdditiveGroup<T>;

template <typename T>
concept CancellableMonoid =
    OrderedAdditiveMonoid<T> &&
    requires (const T& a, const T& b) {
        { a - b } -> T
        // all(a, b) in T : b <= a => a - b is defined and (a - b) + b == a
    };

template <typename T>
concept ArchimedeanMonoid = CancellableMonoid<T>;
    // all(a, b) in T : (a >= 0 and b > 0) => slow_remainder(a, b) terminates
    // QuotientType : ArchimedeanMonoid -> Integer

template <typename T>
concept HalvableMonoid =
    ArchimedeanMonoid<T> &&
    requires (const T& a) {
        { half(a) } -> T
        // all(a, b) in T : (b > 0 and a == b + b) => half(a) == b
    };

template <typename T>
concept EuclideanMonoid = ArchimedeanMonoid<T>;
    // all(a, b) in T : (a > 0 and b > 0) => subtractive_gcd_nonzero(a, b) terminates

template <typename T>
concept EuclideanSemiring = CommutativeSemiring<T>;
    // NormType : EucledianSemiring -> Integer
    // w : T -> NormType(T)
    // all(a) in T : w(a) >= 0
    // all(a) in T : w(a) == 0 <=> a == 0
    // all(a, b) in T : b != 0 => w(a * b) >= w(a)
    // remainder : T * T -> T
    // quotient : T * T -> T
    // all(a, b) in T : b != 0 => a == quotient(a, b) * b + remainder(a, b)
    // all(a, b) in T : b != 0 => w(remainder(a, b)) < w(b)

template <typename T, typename S>
concept EuclideanSemimodule = Semimodule<T, S>;
    // && requires (T& a, T& b) {
    //     { remainder(a, b) } -> T
    //     { quotient(a, b) } -> T
    //     all(a, b) in T : b != 0 => a = quotient(a, b) * b + remainder(a, b)
    //     all(a, b) in T : (a != 0 or b != 0) => gcd(a, b) terminates
    // };

template <typename T>
concept ArchimedeanGroup = ArchimedeanMonoid<T> && AdditiveGroup<T>;

template <typename T>
concept DiscreteArchimedeanSemiring = CommutativeSemiring<T> && ArchimedeanMonoid<T>;
    // all(a, b, c) in T : a < b and 0 < c => a * c < b * c
    // not(exists(a) in T) : 0 < a < 1

template <typename T>
concept NonnegativeDiscreteArchimedeanSemiring = DiscreteArchimedeanSemiring<T>;
    // all(a in T) : 0 <= a

template <typename T>
concept DiscreteArchimedeanRing = DiscreteArchimedeanSemiring<T> && AdditiveGroup<T>;

// Chapter 6: Iterators

template <typename T>
concept Readable =
    Regular<T> &&
    Regular<ValueType<T>> &&
    requires (T a) {
        { source(a) } -> ValueType<T>
    };

template <typename T>
concept Iterator =
    Regular<T> &&
    // DistanceType : Iterator -> Integer
    requires (T a) {
        { successor(a) } -> T
        // successor is not necessarily regular
    };

template <typename I>
concept ReadableIterator = Readable<I> && Iterator<I>;

template <typename T>
concept ForwardIterator = Iterator<T>;
    // regular_unary_function(successor)

template <typename I>
concept ReadableForwardIterator = Readable<I> && ForwardIterator<I>;

template <typename T>
concept IndexedIterator =
    ForwardIterator<T> &&
    requires (T a, DistanceType<T> b) {
        { a + b } -> T
        // { a - c } -> T // - : T * T -> DistanceType(T)
    };
    // + takes constant time
    // - takes constant time

template <typename I>
concept ReadableIndexedIterator = Readable<I> && IndexedIterator<I>;

template <typename T>
concept BidirectionalIterator = ForwardIterator<T>;
    // { predecessor(a) } -> T
    // predecessor takes constant time
    // all(i) in T : successor(i) is defined =>
    //     predecessor(successor(i)) is defined and equals i
    // all(i) in T : predecessor(i) is defined =>
    //     successor(predecessor(i)) is defined and equals i

template <typename I>
concept ReadableBidirectionalIterator = Readable<I> && BidirectionalIterator<I>;

template <typename T>
concept RandomAccessIterator =
    IndexedIterator<T> &&
    BidirectionalIterator<T> &&
    ForwardIterator<T> &&
    TotallyOrdered<T> &&
    requires (T a, DistanceType<T> b) {
        // all(i, j) in T : i < j <=> i < j
        // DifferenceType : RandomAccessIterator -> Integer
        { a + b } -> T
        // - : T * DifferenceType(T) -> T
        // - : T * T -> DifferenceType(T)
        // < takes constant time
        // - between an iterator and an integer takes constant time
    };

// Chapter 7: Coordinate structures

template <typename T>
concept BifurcateCoordinate =
    Regular<T> &&
    Integer<WeightType<T>> &&
    requires (T a) {
        { empty(a) } -> bool
        { has_left_successor(a) } -> bool
        { has_right_successor(a) } -> bool
        { left_successor(a) } -> T
        { right_successor(a) } -> T
        // all(i, j) in T : (left_successor(i) == j or right_successor(i) == j) >= not(empty(i))
    };

template <typename C>
concept ReadableBifurcateCoordinate = Readable<C> && BifurcateCoordinate<C>;

template <typename T>
concept BidirectionalBifurcateCoordinate =
    BifurcateCoordinate<T> &&
    requires(T a) {
        { has_predecessor(a) } -> bool
        // all(i) in T : not(empty(i)) => has_predecessor(i) is defined
        { predecessor(a) } -> T
        // all(i) in T : has_left_successor(i) => predecessor(left_successor(i)) is defined and equals i
        // all(i) in T : has_right_successor(i) => predecessor(right_successor(i)) is defined and equals i
        // all(i) in T : has_predecessor(i) => is_left_successor(i) or is_right_successor(i)
    };

template <typename C>
concept ReadableBidirectionalBifurcateCoordinate = Readable<C> && BidirectionalBifurcateCoordinate<C>;

template <typename F>
concept Comparator3Way = HomogeneousFunction<F> && Arity<F> == 2;
    //  /\ Codomain(F) = int

template <typename F>
concept LinkedForwardIterator = true;

template <typename F>
concept LinkedBidirectionalIterator = true;

template <typename F>
concept UnaryPseudoPredicate = true;

template <typename F>
concept PseudoRelation = true;

// Chapter 8: Coordinates with Mutable Successors

template <typename S>
concept ForwardLinker = ForwardIterator<IteratorType<S>>;
    // Let I = IteratorType<S> in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if successor(i) is defined,
    //         then s(i, j) establishes successor(i) == j

template <typename S>
concept BackwardLinker = BidirectionalIterator<IteratorType<S>>;
    // Let I = IteratorType<S> in:
    //     all(s) in S : (s : I * I -> void)
    //     all(s) in S : all(i, j) in I if prececessor(i) is defined,
    //         then s(i, j) establishes i == predecessor(j)

template <typename S>
concept BidirectionalLinker = ForwardLinker<S> && BackwardLinker<S>;

template <typename T>
concept LinkedBifurcateCoordinate =
    BifurcateCoordinate<T> &&
    requires (T a) {
        { set_left_successor(a, a) } -> void
        //     (i, j) -> establishes left_successor(i) == j
        { set_right_successor(a, a) } -> void
        //     (i, j) -> establishes right_successor(i) == j
    };

template <typename T>
concept EmptyLinkedBifurcateCoordinate =
    LinkedBifurcateCoordinate<T> &&
    requires(T a) {
        empty(a);
        // empty(T()) (In other words, empty is true on the default constructed value and possibly on other values as well)
        // not(empty(i)) => left_successor(i) and right_successor(i) are defined
        // not(empty(i)) => (not(has_left_successor(i) <=> empty(left_successor(i))))
        // not(empty(i)) => (has_right_successor(i) <=> empty(right_successor(i))))
    };

// Chapter 9: Copying

template <typename T>
concept Writable =
    Regular<ValueType<T>> &&
    requires(T x) {
        sink(x);
        // all(x in T) : (all(v) in ValueType<T>) : sink(x) <- v is a well-formed statement
    };

template <typename O>
concept WritableIterator = Writable<O> && Iterator<O>;

template <typename I>
concept WritableForwardIterator = Writable<I> && ForwardIterator<I>;

template <typename I>
concept WritableBidirectionalIterator = Writable<I> && BidirectionalIterator<I>;

template <typename T>
concept Mutable =
    Readable<T> &&
    Writable<T> &&
    requires(T x) {
        sink(x);
        source(x);
        // all(x) in T : sink(x) is defined <=> source(x) is defined
        // all(x) in T : sink(x) is defined => aliased(x, x)
        { deref(x) } -> ValueType<T>&
        // all(x) in T : sink(x) is defined <=> deref(x) is defined
    };

template <typename I>
concept MutableForwardIterator = Mutable<I> && ForwardIterator<I>;

template <typename I>
concept MutableBidirectionalIterator = Mutable<I> && BidirectionalIterator<I>;

template <typename I>
concept MutableIndexedIterator = Mutable<I> && IndexedIterator<I>;

template<typename I>
concept MutableRandomAccessIterator = Mutable<I> && RandomAccessIterator<I>;

// Chapter 12: Composite Objects

template <typename W>
concept Linearizable =
    Regular<W> &&
    // IteratorType : Linearizable -> Integer
    Regular<ValueType<W>> &&
    //     W -> ValueType<IteratorType<W>>
    Integer<SizeType<W>> &&
    //     W -> DistanceType(IteratorType<W>)
    requires(W x) {
        { begin(x) } -> IteratorType<W>
        { end(x) } -> IteratorType<W>
        // { size(x) } -> SizeType<W>
        //     x -> end(x) - begin(x)
        // { empty(x) } -> bool
        //     x -> begin(x) == end(x)
        // [] : W * SizeType<W> -> ValueType<W>&
        //     (w, i) -> deref(begin(w) + i)
    };

template <typename S>
concept Sequence =
    Linearizable<S> &&
    requires(S x) {
        begin(x);
        end(x);
        // all(s) in S : all(i) in [begin(s), end(s))) deref(i) is a part of s
        // = : S * S -> bool
        //     (s, s') -> lexicographical_equal(begin(s), end(s), begin(s'), end(s'))
        // < : S * S -> bool
        //     (s, s') -> lexicographical_less(begin(s), end(s), begin(s'), end(s'))
    };

template <typename S>
concept BinaryPredicate = true;

template <typename T>
concept Position =
    Linearizable<BaseType<T>> &&
    Iterator<IteratorType<T>> &&
    Regular<ValueType<T>> &&
    //         T |- ValueType<IteratorType<T>>
    Integer<SizeType<T>> &&
    //         T |- SizeType<IteratorType<T>>
    requires(T x) {
        { base(x) } -> BaseType<T>
        { current(x) } -> IteratorType<T>
        { begin(x) } -> IteratorType<T>
        //         x |- begin(base(x))
        { end(x) } -> IteratorType<T>
        //         x |- end(base(x))
    };

template <typename T>
concept DynamicSequence = Sequence<T>;
    //  /\ T supports insert and erase

template <typename T>
concept InsertPosition = Position<T> && DynamicSequence<BaseType<T>>;

template <typename T>
concept ErasePosition = Position<T> && DynamicSequence<BaseType<T>>;

template <typename T, typename U>
concept Destroyable = true;

template <typename T>
concept TreeNodeConstructor = true;

template <typename T>
concept TreeNodeDeleter = true;

#endif // EOP_CONCEPTS
