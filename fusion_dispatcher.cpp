// (C) Copyright Tobias Schwinger
//
// Use modification and distribution are subject to the boost Software License,
// Version 1.0. (See http://www.boost.org/LICENSE_1_0.txt).

//------------------------------------------------------------------------------
//
// The problem:
//
//  Call one of a heterogenous set of functors (their call operators might 
//  templates) based on a runtime index. Generate code like an n-ary tree of 
//  nested switch/case blocks.
//
// Note:
// 
//  This code needs an MPL patch to make mpl::is_sequence work (well, 
//  at least sort-of) properly [ http://tinyurl.com/ljfdm ] to compile.
//
// Disclaimer:
// 
//  This software is written for evaluation purposes. Please neither expect it
//  to be practical nor elegant.
//
// Hint:
//
//  Read from bottom to top.
//
// Known to compile with VisualC++ 7.1 / 8.0
//
//------------------------------------------------------------------------------

#include <boost/mpl/list.hpp>
#include <boost/mpl/fold.hpp>
#include <boost/mpl/if.hpp>
#include <boost/mpl/eval_if.hpp>
#include <boost/mpl/identity.hpp>
#include <boost/mpl/pair.hpp>
#include <boost/mpl/joint_view.hpp>
#include <boost/mpl/range_c.hpp>
#include <boost/mpl/size.hpp>
#include <boost/mpl/integral_c.hpp>
#include <boost/mpl/bool.hpp>
#include <boost/mpl/int.hpp>

#include <boost/mpl/list.hpp>
#include <boost/mpl/push_front.hpp>

#include <boost/mpl/next.hpp>
#include <boost/mpl/prior.hpp>
#include <boost/mpl/plus.hpp>
#include <boost/mpl/shift_left.hpp>
#include <boost/mpl/times.hpp>
#include <boost/mpl/less.hpp>
#include <boost/mpl/less_equal.hpp>
#include <boost/mpl/equal_to.hpp>

#include <boost/fusion/sequence/container/list/cons.hpp>
#include <boost/fusion/sequence/adapted/mpl.hpp>
#include <boost/fusion/sequence/intrinsic/at.hpp>
#include <boost/fusion/sequence/intrinsic/value_at.hpp>
#include <boost/fusion/sequence/intrinsic/begin.hpp>
#include <boost/fusion/sequence/intrinsic/end.hpp>
#include <boost/fusion/iterator/next.hpp>
#include <boost/fusion/iterator/deref.hpp>
#include <boost/fusion/iterator/equal_to.hpp>
#include <boost/fusion/algorithm/iteration/fold.hpp>
#include <boost/fusion/algorithm/transformation/push_back.hpp>
#include <boost/fusion/sequence/io/out.hpp>
#include <boost/fusion/support/is_sequence.hpp>
#include <boost/fusion/support/pair.hpp>

#include <boost/fusion/sequence/container/vector.hpp>

namespace meta
{
  using namespace boost::mpl;
  using namespace boost::mpl::placeholders;

  // split sequence into sequence of sequences with N elements each
  // remaining elements are kept in the top-level sequence
  template<typename Seq, typename N>
  struct split;

  template<typename Seq, typename N>
  struct split_impl
    : fold
      < Seq
      , pair< list0<>, list0<> >
      , if_< less< size < second<_1> >, N >
           , pair< first<_1>, push_front< second<_1>, _2 > >
           , pair< push_front< first<_1>, second<_1> >, list1<_2> >
           >
      >::type
  { };

  template<typename Seq, typename N>
  struct split
    : joint_view< typename split_impl<Seq,N>::first  
                , typename split_impl<Seq,N>::second >::type
  { };

  // apply split (above) until the top-level sequence contains no more
  // than N elements
  template<typename Seq, typename N>
  struct treeize
    : if_< less_equal< size< split<Seq,N> >, N >
         , split<Seq,N>, treeize< split<Seq,N>, N > >::type
  { };


  // compile time logarithm, base 2
  template<class X> struct log2;

  template<typename VT>
  struct log2_impl
  {
    template<VT X, VT N = 0> struct linear
      : linear< (X >> 1), (N+1) >
    { };

    template<std::size_t N> struct linear<1,N> 
      : integral_c<VT,N>
    { };
  };

  template<class X>
  struct log2
    : log2_impl<typename X::value_type>::template linear<X::value,0>
  { };

  template<class X>
  struct ceil_log2
    : log2_impl<typename X::value_type>::template linear<X::value*2-1,0>
  { };

  // Nth power of two
  template<class N> 
  struct exp2
    : shift_left<integral_c<typename N::value_type, 1>, N>
  { };

  // tree addressing
  //
  //                   o       o         <-- least significant bits
  //                  / \     / \
  //                 o   o   o   o       V-- most significant bits
  //
  template<class TreeIndex> struct index            : TreeIndex::i      { };
  template<class TreeIndex> struct vertical_next    : TreeIndex::vnext  { };
  template<class TreeIndex> struct horizontal_next  : TreeIndex::hnext  { };
  template<class TreeIndex> struct mask_index_pair  : TreeIndex::m_i_p  { };
  template<
    class BitWidth
  , class Depth  = integral_c<typename BitWidth::value_type,0> 
  , class Index  = integral_c<typename BitWidth::value_type,0> >
  struct tree_index
  {
    typedef tree_index type;

    typedef BitWidth b;
    typedef Depth    d;
    typedef Index    i;

    typedef tree_index<b,d,plus<i, exp2< times<d,b> > > >  hnext;
    typedef tree_index<b,typename next<d>::type,i>         vnext;

    typedef 
      pair< typename prior< exp2< times<typename next<d>::type,b> > >::type, i >
    m_i_p;
  };


  // lookup node id by index
  template<typename Tree, typename TreeIndex, typename I>
  struct find_index;

  template<typename Tree, typename TreeIndex, typename I>
  struct find_index_impl
    : fold
      < Tree
      , pair<TreeIndex, false_>
      , if_
        < second<_1>
        , _1
        , if_
          < is_sequence<_2>
          , if_
            < second< find_index_impl<_2,vertical_next< first<_1> >, I> >
            , find_index_impl<_2,vertical_next< first<_1> >, I>
            , pair< horizontal_next< first<_1> >, false_>
            >
          , if_
            < equal_to<_2,I>
            , pair< first<_1>, true_ >
            , pair< horizontal_next< first<_1> >, false_ >
            >
        > > 
      > ::type
  { };

  template<typename Tree, typename TreeIndex, typename I>
  struct find_index
    : index< typename first< find_index_impl<Tree,TreeIndex,I> >::type >
  { };

}

namespace wknd
{
  // conceptually differences between MPL and Fusion pairs
  template<class FusionPair> struct first
  {
    typedef typename FusionPair::first_type type;
  };

  template<class FusionPair> struct second
  {
    typedef typename FusionPair::second_type type;
  };

  // missing result metafunction for fusion::make_pair
  template<typename First, typename Second>
  struct result_of_make_pair
  {
    typedef boost::fusion::pair<First, 
      typename boost::fusion::detail::as_fusion_element<Second>::type> type;
  };

  // vector::at_impl requires mpl::int_ specialization bug 
  template<typename IntegralConstant>
  struct force_mpl_int
    : boost::mpl::int_< IntegralConstant::value >
  { };

}

namespace con_fusion
{
  namespace mpl = boost::mpl;
  namespace fusion = boost::fusion;
  namespace result_of = boost::fusion::result_of;
  namespace traits = boost::fusion::traits;
  using namespace mpl::placeholders;

  // creates the tree structure for the dispatcher, that is a fusion sequence
  // of fusion pairs< index_info >( functor/child_sequence ).
  template<typename DispatchTable>
  class dispatch_tree_builder
  {
    DispatchTable const & ref_dispatch_table;
  public:

    dispatch_tree_builder(DispatchTable const & dispatch_table)
      : ref_dispatch_table(dispatch_table)
    { }

    dispatch_tree_builder(dispatch_tree_builder const & that)
      : ref_dispatch_table(that.ref_dispatch_table)
    { }

  private:

    struct node_op
    {
      template<class Element, class State>
      struct result
        : mpl::apply2
          < wknd::result_of_make_pair
            < meta::horizontal_next< wknd::first<_2> >
            , result_of::push_back
              < boost::add_const< wknd::second<_2> >
              , wknd::result_of_make_pair
                < meta::mask_index_pair< wknd::first<_2> >
                , wknd::second
                  < result_of::fold
                    < _1
                    , wknd::result_of_make_pair
                      < meta::vertical_next< wknd::first<_2> >, fusion::nil >
                    , dispatch_tree_builder
            > > > > >
          , Element, State
          >
      { };

      template<class Element, class State>
      static inline typename result<Element,State>::type
      call(Element const & e, State const & s, dispatch_tree_builder const & me)
      {
        typedef typename State::first_type tree_index;

        return 
          fusion::make_pair<typename meta::horizontal_next<tree_index>::type>
          ( fusion::push_back
            ( s.second
            , fusion::make_pair
              < typename meta::mask_index_pair<tree_index>::type >
              ( fusion::fold
                ( e
                , fusion::make_pair
                  < typename meta::vertical_next<tree_index>::type >
                  ( fusion::nil() )
                , me
                ).second
          ) ) );
      }
    };

    struct leaf_op
    {
      template<class Element, class State>
      struct result
        : mpl::apply2
          < wknd::result_of_make_pair
            < meta::horizontal_next< wknd::first<_2> >
            , result_of::push_back
              < boost::add_const< wknd::second<_2> >
              , wknd::result_of_make_pair
                < meta::index< wknd::first<_2> >
                , result_of::value_at<DispatchTable, wknd::force_mpl_int<_1> > 
              > >
            >
          , Element, State>
      { };

      template<class Element, class State>
      static inline typename result<Element,State>::type
      call(Element const &, State const & s, dispatch_tree_builder const & me)
      {
        typedef typename wknd::first<State>::type tree_index;

        return 
          fusion::make_pair<typename meta::horizontal_next<tree_index>::type>
          ( fusion::push_back
            ( s.second 
            , fusion::make_pair<typename meta::index<tree_index>::type>
              ( fusion::at<typename wknd::force_mpl_int<Element>::type>
                ( me.ref_dispatch_table ) 
          ) ) );
      }

    };

    template<class Element>
    struct select_op
      : mpl::if_< mpl::is_sequence<Element>
                , node_op, leaf_op >::type
    { };

  public:

    template<class Element, class State>
    struct result
      : select_op<Element>::template result<Element,State>
    { }; 

    template<class Element, class State>
    inline typename result<Element,State>::type
    operator()(Element const & element, State const & state) const
    {
      return select_op<Element>::call(element,state,*this);
    }

  };

  // the dispatcher traverses the tree with iterators 
  template<typename DispatchTable, int N>
  class dispatcher
  {
    typedef mpl::range_c<int,0,result_of::size<DispatchTable>::value> indices;
    typedef mpl::integral_c<int,N>             tree_arity;

    typedef meta::ceil_log2<tree_arity>        bit_width;

    typedef meta::treeize<indices,tree_arity>  meta_tree;
    typedef meta::tree_index<bit_width>        tree_index;

    typedef 
      typename mpl::apply1 
      < wknd::second
        < result_of::fold
          < meta_tree const
          , wknd::result_of_make_pair<tree_index, _>
          , dispatch_tree_builder<DispatchTable>
        > > 
      , fusion::nil 
      >::type
    tree;

    tree tpl_tree;

  public:

    // ctor builds the dispatch tree
    dispatcher(DispatchTable const & dispatch_table)
      : tpl_tree
        ( fusion::fold
          ( meta_tree() 
          , fusion::make_pair<tree_index>(fusion::nil())
          , dispatch_tree_builder<DispatchTable>(dispatch_table)
          ).second
        )
    { }

  private:

    // decision making for leaf | node | end

    struct leaf_op;
    struct node_op;
    struct no_op;

    template<typename IterationContext> struct at_node
      : traits::is_sequence
        < typename wknd::second
          < typename result_of::deref
            <typename IterationContext::second_type>::type
          >::type
        >
    { };

    template<typename IterationContext> struct at_end
      : result_of::equal_to
        < typename IterationContext::first_type 
        , typename IterationContext::second_type
        >
    { };

    template<typename IterationContext> struct select_op
      : mpl::eval_if
        < at_end<IterationContext>
        , mpl::identity< no_op >
        , mpl::if_<at_node<IterationContext>, node_op, leaf_op>
        >::type
    { };

    template<typename IterationContext, typename T>
    static inline void dispatch
          (IterationContext const & there, int id, T const & arg)
    {
      select_op<IterationContext>::call(there,id,arg);
    }

    // call the functor if the dispatch id matches or continue searching
    struct leaf_op
    {
      template<typename IterationContext, typename T>
      static inline void call
          (IterationContext const & there, int id, T const & arg)
      {
        typedef typename IterationContext::first_type end;
        typedef typename IterationContext::second_type current_position;
        typedef typename result_of::deref<current_position>::type dispatch_info;
        typedef typename dispatch_info::first_type index;

        if (id == index::value)
          // no operator-> for fusion iterators??
          (*there.second).second(arg);
        else
          dispatcher::dispatch
          ( fusion::make_pair<end>(fusion::next(there.second)), id, arg );
      } 

      template<typename IterationContext> struct result { typedef void type; };
    };

    // recurse if the current element contains the leaf or continue searching
    struct node_op
    {
      template<typename IterationContext, typename T>
      static inline void call
          (IterationContext const & there, int id, T const & arg)
      {
        typedef typename IterationContext::first_type end;
        typedef typename IterationContext::second_type current_position;
        typedef typename result_of::deref<current_position>::type dispatch_info;
        typedef typename dispatch_info::first_type mask_index_pair;
        typedef typename dispatch_info::second_type children;
        typedef typename mpl::first<mask_index_pair>::type mask;
        typedef typename mpl::second<mask_index_pair>::type index;
        typedef typename result_of::end<children>::type children_end;

        if ((id & mask::value) == index::value)
          dispatcher::dispatch
          ( fusion::make_pair<children_end>
            // no operator-> for fusion iterators??
            ( fusion::begin((*there.second).second) )
          , id
          , arg 
          );
        else
          dispatcher::dispatch
          ( fusion::make_pair<end>(fusion::next(there.second)), id, arg );
      }
    };

    // terminator (used when iterators are equal)
    struct no_op
    {
      template<typename IterationContext, typename T>
      static inline void call(IterationContext const &, int, T const &)
      { }
    };

  public:

    // operator() passes on a single argument and has no return value for the
    // sake of simplicity
    template<typename T>
    inline void operator()(int id, T const & arg)
    {
      typedef typename result_of::end<tree>::type end;

      dispatch
      ( fusion::make_pair<end>(fusion::begin(this->tpl_tree)), id, arg );
    }

    // numeric metafunction to get the dispatch id (the one that has to be 
    // passed to operator()) for a given index
    template<int I> struct id
      : meta::find_index< meta_tree,tree_index, mpl::int_<I> >
    { };
  };
}


//---[ test case ]--------------------------------------------------------------

#include <typeinfo>
#include <iostream>

// a test functor
// - it's a class template so it can be instantiated to distinct types
// - it;s stateful for testing the state does not get lost
// - it has a templated oprator() so type preservation is transparent

template<int I>
class func
{
  int val_ordinal;
public:

  func(int ordinal)
    : val_ordinal(ordinal)
  { }

  template<typename T>
  void operator()(T const & t) const
  {
    std::cout << typeid(func).name() << "::operator()(T)";
    std::cout << " [ ordinal = " << this->val_ordinal;
    std::cout << " T = " << typeid(T).name() << " ]" << std::endl;
  }
};

int main()
{
  // tuple with test functors (note: all have different types and a templated
  // call operator)

  typedef boost::fusion::vector
  < func<7>,func<6>,func<5>,func<4>,func<3>,func<2>,func<1>,func<0> > functors;

  functors f(0,1,2,3,4,5,6,7);

  // create a tree dispatcher that uses a ternary tree

  typedef con_fusion::dispatcher<functors,3> dispatcher;
  dispatcher d(f); 

  // get the dispatch ids by value

  int id[] = 
  { dispatcher::template id<0>::value
  , dispatcher::template id<1>::value
  , dispatcher::template id<2>::value
  , dispatcher::template id<3>::value
  , dispatcher::template id<4>::value
  , dispatcher::template id<5>::value
  , dispatcher::template id<6>::value
  , dispatcher::template id<7>::value
  };

  // call the stored functions (note: this beast is entirely type preserving!!)

  for (int i = 0; i < 8; ++i)
  {
    d(id[i], 0);
    d(id[i], 0L);
  }

  return 0;
}

