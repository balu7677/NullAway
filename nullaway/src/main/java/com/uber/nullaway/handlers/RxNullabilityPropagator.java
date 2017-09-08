/*
 * Copyright (c) 2017 Uber Technologies, Inc.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package com.uber.nullaway.handlers;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.VisitorState;
import com.google.errorprone.dataflow.nullnesspropagation.Nullness;
import com.google.errorprone.predicates.TypePredicate;
import com.google.errorprone.predicates.type.DescendantOf;
import com.google.errorprone.suppliers.Suppliers;
import com.google.errorprone.util.ASTHelpers;

import com.sun.source.tree.BlockTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.uber.nullaway.NullAway;
import com.uber.nullaway.NullabilityUtil;
import com.uber.nullaway.dataflow.AccessPath;
import com.uber.nullaway.dataflow.AccessPathNullnessAnalysis;
import com.uber.nullaway.dataflow.NullnessStore;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.Tree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;

import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.LocalVariableNode;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * This Handler transfers nullability info through chains of calls to methods of io.reactivex.Observable.
 *
 * This allows the checker to know, for example, that code like the following has no NPEs:
 * observable.filter(... return o.foo() != null; ...).map(... o.foo.toString() ...)
 */
class RxNullabilityPropagator extends BaseNoOpHandler {

    private final ImmutableList<StreamTypeRecord> RX_MODELS =
            StreamModelBuilder.start()
                .addStreamType(new DescendantOf(Suppliers.typeFromString("io.reactivex.Observable")))
                    // Names of all the methods of io.reactivex.Observable that behave like .filter(...)
                    // (must take exactly 1 argument)
                    .withFilterMethodFromSignature("filter(io.reactivex.functions.Predicate<? super T>)")
                    // Names and relevant arguments of all the methods of io.reactivex.Observable that behave like
                    // .map(...) for the purposes of this checker (the listed arguments are those that take the
                    // potentially filtered objects from the stream)
                    .withMapMethodFromSignature(
                            "<R>map(io.reactivex.functions.Function<? super T,? extends R>)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,boolean)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,boolean,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,boolean,int,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,"
                                    + "io.reactivex.functions.Function<? super Throwable,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,"
                                    + "java.util.concurrent.Callable<? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? "
                                    + "extends io.reactivex.ObservableSource<? extends R>>,"
                                    + "io.reactivex.functions.Function<Throwable,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,"
                                    + "java.util.concurrent.Callable<? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends R>>,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<U,R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends U>>,"
                                    + "io.reactivex.functions.BiFunction<? super T,? super U,? extends R>)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<U,R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends U>>,"
                                    + "io.reactivex.functions.BiFunction<? super T,? super U,? extends R>,boolean)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<U,R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends U>>,"
                                    + "io.reactivex.functions.BiFunction<? super T,? super U,? extends R>,boolean,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<U,R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends U>>,"
                                    + "io.reactivex.functions.BiFunction<? super T,? super U,? extends R>,"
                                    + "boolean,int,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<U,R>flatMap(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.ObservableSource<? extends U>>,"
                                    + "io.reactivex.functions.BiFunction<? super T,? super U,? extends R>,int)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMapSingle(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.SingleSource<? extends R>>)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "<R>flatMapSingle(io.reactivex.functions.Function<? super T,? extends "
                                    + "io.reactivex.SingleSource<? extends R>>,boolean)",
                            "apply",
                            ImmutableSet.of(0))
                    .withMapMethodFromSignature(
                            "distinctUntilChanged(io.reactivex.functions.BiPredicate<? super T,? super T>)",
                            "test",
                            ImmutableSet.of(0, 1))
                    // List of methods of io.reactivex.Observable through which we just propagate the nullability
                    // information of the last call, e.g. m() in Observable.filter(...).m().map(...) means the
                    // nullability information from filter(...) should still be propagated to map(...), ignoring the
                    // interleaving call to m().
                    .withPassthroughMethodFromSignature("distinct()")
                    .withPassthroughMethodFromSignature("distinctUntilChanged()")
                    .withPassthroughMethodFromSignature("observeOn(io.reactivex.Scheduler)")
                    .withPassthroughMethodFromSignature("observeOn(io.reactivex.Scheduler,boolean)")
                    .withPassthroughMethodFromSignature("observeOn(io.reactivex.Scheduler,boolean,int)")
                .addStreamType(new DescendantOf(Suppliers.typeFromString("io.reactivex.Maybe")))
                    .withFilterMethodFromSignature("filter(io.reactivex.functions.Predicate<? super T>)")
                    .withMapMethodFromSignature(
                            "<R>map(io.reactivex.functions.Function<? super T,? extends R>)",
                            "apply",
                            ImmutableSet.of(0))
                .addStreamType(new DescendantOf(Suppliers.typeFromString("io.reactivex.Single")))
                    .withFilterMethodFromSignature("filter(io.reactivex.functions.Predicate<? super T>)")
                    .withMapMethodFromSignature(
                            "<R>map(io.reactivex.functions.Function<? super T,? extends R>)",
                            "apply",
                            ImmutableSet.of(0))
            .end();

    /* Terminology for this class internals:
     *
     * Assume the following observable chain:
     *
     * observable.filter(new A() {
     *      public boolean filter(T o) {
     *          ...
     *      }
     * }.map(new B() {
     *      public T apply(T o) {
     *          ...
     *      }
     * }
     *
     * We call:
     *   - A.filter - The filter method (not Observable.filter)
     *   - B.apply - The map method (not Observable.map)
     *   - observable.filter().map() is the observable call chain, and 'Observable.map' is the outer call of
     *   'Observable.filter'). In general, for observable.a().b().c(), c is the outer call of b and b the outer call
     *   of a in the chain.
     *
     * This class works by building the following maps which keep enough state outside of the standard dataflow
     * analysis for us to figure out what's going on:
     *
     * Note: If this state ever becomes a memory issue, we can discard it as soon as we exit any method at the
     * topmost scope (e.g. not a method called from an anonymous inner class inside another method or a lambda).
     */

    // Set of filter methods found thus far (e.g. A.filter, see above)
    private Set<MethodTree> filterMethodsSet = new LinkedHashSet<MethodTree>();

    // Maps each call in the observable call chain to its outer call (see above).
    private Map<MethodInvocationTree, MethodInvocationTree> observableOuterCallInChain = new
            LinkedHashMap<MethodInvocationTree, MethodInvocationTree>();

    // Maps the call in the observable call chain to the relevant functor method.
    // e.g. In the example above:
    //   observable.filter() => A.filter
    //   observable.filter().map() => B.apply
    private Map<MethodInvocationTree, MethodTree> observableCallToActualFunctorMethod = new
            LinkedHashMap<MethodInvocationTree, MethodTree>();

    // Map from map method to corresponding previous filter method (e.g. B.apply => A.filter)
    private Map<MethodTree, MaplikeToFilterInstanceRecord> mapToFilterMap =
            new LinkedHashMap<MethodTree, MaplikeToFilterInstanceRecord>();

    /*
     * Note that the above methods imply a diagram like the following:
     *
     *                              /--- observable.filter(new A() {
     *                              |      \->public boolean filter(T o) {<---\
     * [observableOuterCallInChain] |             ...                         |
     *                              |         }                               | [mapToFilterMap]
     *                              \--> }.map(new B() {                      |
     *                                     \->public T apply(T o) {        ---/
     *                                            ...
     *                                        }
     *                                   }
     */

    // Map from filter method to corresponding nullability info after the method returns true.
    // Specifically, this is the least upper bound of the "then" store on the branch of every return statement in
    // which the expression after the return can be true.
    private Map<MethodTree, NullnessStore<Nullness>> filterToNSMap =
            new LinkedHashMap<MethodTree, NullnessStore<Nullness>>();

    // Maps the method body to the corresponding method tree, used because the dataflow analysis loses the pointer
    // to the MethodTree by the time we hook into it.
    private Map<BlockTree, MethodTree> blockToMethod = new LinkedHashMap<BlockTree, MethodTree>();

    // Maps the return statements of the filter method to the filter tree itself, similar issue as above.
    private Map<ReturnTree, MethodTree> returnToMethod = new LinkedHashMap<ReturnTree, MethodTree>();

    RxNullabilityPropagator() {
        super();
    }

    @Override
    public void onMatchTopLevelClass(
            NullAway analysis,
            ClassTree tree,
            VisitorState state,
            Symbol.ClassSymbol classSymbol) {
        // Clear compilation unit specific state
        this.filterMethodsSet.clear();
        this.observableOuterCallInChain.clear();
        this.observableCallToActualFunctorMethod.clear();
        this.mapToFilterMap.clear();
        this.filterToNSMap.clear();
        this.blockToMethod.clear();
        this.returnToMethod.clear();
    }

    @Override
    public void onMatchMethodInvocation(
            NullAway analysis,
            MethodInvocationTree tree,
            VisitorState state,
            Symbol.MethodSymbol methodSymbol) {
        Type receiverType = ASTHelpers.getReceiverType(tree);
        for(StreamTypeRecord streamType : RX_MODELS) {
            if (streamType.matchesType(receiverType, state)) {
                String methodName = methodSymbol.toString();

                // Build observable call chain
                buildObservableCallChain(tree);

                // Dispatch to code handling specific observer methods
                if (streamType.isFilterMethod(methodName) && methodSymbol.getParameters().length() == 1) {
                    ExpressionTree argTree = tree.getArguments().get(0);
                    if (argTree instanceof NewClassTree) {
                        ClassTree annonClassBody = ((NewClassTree) argTree).getClassBody();
                        // Ensure that this `new A() ...` has a custom class body, otherwise, we skip for now.
                        // In the future, we could look at the declared type and its inheritance chain, at least for
                        // filters.
                        if (annonClassBody != null) {
                            handleFilterAnonClass(streamType, tree, annonClassBody, state);
                        }
                    }
                    // This can also be a lambda, which currently cannot be used in the code we look at, but might be
                    // needed by others. Add support soon.
                } else if (streamType.isMapMethod(methodName) && methodSymbol.getParameters().length() == 1) {
                    ExpressionTree argTree = tree.getArguments().get(0);
                    if (argTree instanceof NewClassTree) {
                        ClassTree annonClassBody = ((NewClassTree) argTree).getClassBody();
                        // Ensure that this `new B() ...` has a custom class body, otherwise, we skip for now.
                        if (annonClassBody != null) {
                            MaplikeMethodRecord methodRecord = streamType.getMaplikeMethodRecord(methodName);
                            handleMapAnonClass(methodRecord, tree, annonClassBody, state);
                        }
                    }
                    // This can also be a lambda, which currently cannot be used in the code we look at, but might be
                    // needed by others. Add support soon.
                }
            }
        }
    }

    private void buildObservableCallChain(MethodInvocationTree tree) {
        ExpressionTree methodSelect = tree.getMethodSelect();
        if (methodSelect instanceof MemberSelectTree) {
            ExpressionTree receiverExpression = ((MemberSelectTree) methodSelect).getExpression();
            if (receiverExpression instanceof MethodInvocationTree) {
                observableOuterCallInChain.put((MethodInvocationTree) receiverExpression, tree);
            }
            // ToDo: Eventually we want to handle more complex observer chains, but filter(...).map(...) is the
            // common case.
        } // ToDo: What else can be here? If there are other cases than MemberSelectTree, handle them.
    }

    private void handleFilterAnonClass(
            StreamTypeRecord streamType,
            MethodInvocationTree observableDotFilter,
            ClassTree annonClassBody,
            VisitorState state) {
        for (Tree t : annonClassBody.getMembers()) {
            if (t instanceof MethodTree
                    && ((MethodTree) t).getName().toString().equals("test")) {
                filterMethodsSet.add((MethodTree) t);
                observableCallToActualFunctorMethod.put(observableDotFilter, (MethodTree) t);
                // Traverse the observable call chain out through any pass-through methods
                MethodInvocationTree outerCallInChain = observableOuterCallInChain.get(observableDotFilter);
                while (outerCallInChain != null
                        && streamType.matchesType(ASTHelpers.getReceiverType(outerCallInChain), state)
                        && streamType.isPassthroughMethod(
                                ASTHelpers.getSymbol(outerCallInChain).toString())) {
                    outerCallInChain = observableOuterCallInChain.get(outerCallInChain);
                }
                // Check for a map method
                MethodInvocationTree mapCallsite = observableOuterCallInChain.get(observableDotFilter);
                if (outerCallInChain != null
                        && observableCallToActualFunctorMethod.containsKey(outerCallInChain)
                        && streamType.matchesType(ASTHelpers.getReceiverType(outerCallInChain), state)) {
                    // Update mapToFilterMap
                    String mapMethodName = ASTHelpers.getSymbol(outerCallInChain).toString();
                    if (streamType.isMapMethod(mapMethodName)) {
                        MaplikeToFilterInstanceRecord record =
                                new MaplikeToFilterInstanceRecord(
                                        streamType.getMaplikeMethodRecord(mapMethodName),
                                        (MethodTree) t);
                        mapToFilterMap.put(observableCallToActualFunctorMethod.get(outerCallInChain), record);
                    }
                }
            }
        }
    }

    private void handleMapAnonClass(
            MaplikeMethodRecord methodRecord,
            MethodInvocationTree observableDotMap,
            ClassTree annonClassBody,
            VisitorState state) {
        for (Tree t : annonClassBody.getMembers()) {
            if (t instanceof MethodTree
                    && ((MethodTree) t).getName().toString().equals(methodRecord.getInnerMethodName())) {
                observableCallToActualFunctorMethod.put(observableDotMap, (MethodTree) t);
            }
        }
    }

    @Override
    public void onMatchMethod(
            NullAway analysis,
            MethodTree tree,
            VisitorState state,
            Symbol.MethodSymbol methodSymbol) {
        if (mapToFilterMap.containsKey(tree)) {
            blockToMethod.put(tree.getBody(), tree);
        }
    }

    private boolean canBooleanExpressionEvalToTrue(ExpressionTree expressionTree) {
        if (expressionTree instanceof LiteralTree) {
            LiteralTree expressionAsLiteral = (LiteralTree) expressionTree;
            if (expressionAsLiteral.getValue() instanceof Boolean) {
                return (boolean) expressionAsLiteral.getValue();
            } else {
                throw new RuntimeException("not a boolean expression!");
            }
        }
        // We are fairly conservative, anything other than 'return false;' is assumed to potentially be true.
        // No SAT-solving or any other funny business.
        return true;
    }

    @Override
    public void onMatchReturn(NullAway analysis, ReturnTree tree, VisitorState state) {
        // Figure out the enclosing method node
        TreePath enclosingMethodOrLambda = NullabilityUtil.findEnclosingMethodOrLambda(state.getPath());
        if (enclosingMethodOrLambda == null) {
            throw new RuntimeException("no enclosing method!");
        }
        Tree leaf = enclosingMethodOrLambda.getLeaf();
        if (leaf instanceof MethodTree) {
            MethodTree enclosingMethod = (MethodTree) leaf;
            if (filterMethodsSet.contains(enclosingMethod)) {
                returnToMethod.put(tree, enclosingMethod);
                // We need to manually trigger the dataflow analysis to run on the filter method,
                // this ensures onDataflowVisitReturn(...) gets called for all return statements in this method before
                // onDataflowMethodInitialStore(...) is called for all successor methods in the observable
                // chain.
                // Caching should prevent us from re-analyzing any given method.
                AccessPathNullnessAnalysis nullnessAnalysis = analysis.getNullnessAnalysis(state);
                nullnessAnalysis.forceRunOnMethod(new TreePath(state.getPath(), enclosingMethod), state.context);
            }
        }
        // This can also be a lambda, which currently cannot be used in the code we look at, but might be needed by
        // others. Add support soon.

    }

    @Override
    public NullnessStore.Builder<Nullness> onDataflowMethodInitialStore(
            UnderlyingAST underlyingAST,
            List<LocalVariableNode> parameters,
            NullnessStore.Builder<Nullness> nullnessBuilder) {
        MethodTree tree = blockToMethod.get((BlockTree) underlyingAST.getCode());
        if (mapToFilterMap.containsKey(tree)) {
            // Plug Nullness info from filter method into entry to map method.
            MaplikeToFilterInstanceRecord callInstanceRecord = mapToFilterMap.get(tree);
            MethodTree filterMethodTree = callInstanceRecord.getFilter();
            MaplikeMethodRecord mapMR = callInstanceRecord.getMaplikeMethodRecord();
            for (int argIdx : mapMR.getArgsFromStream()) {
                LocalVariableNode filterLocalName = new LocalVariableNode(filterMethodTree.getParameters().get(0));
                LocalVariableNode mapLocalName = new LocalVariableNode(tree.getParameters().get(argIdx));
                NullnessStore<Nullness> filterNullnessStore = filterToNSMap.get(filterMethodTree);
                NullnessStore<Nullness> renamedRootsNullnessStore =
                        filterNullnessStore.uprootAccessPaths(ImmutableMap.of(filterLocalName, mapLocalName));
                for (AccessPath ap : renamedRootsNullnessStore.getAccessPathsWithValue(Nullness.NONNULL)) {
                    nullnessBuilder.setInformation(ap, Nullness.NONNULL);
                }
            }
        }
        return nullnessBuilder;
    }

    @Override
    public void onDataflowVisitReturn(
            ReturnTree tree,
            NullnessStore<Nullness> thenStore,
            NullnessStore<Nullness> elseStore) {
        if (returnToMethod.containsKey(tree)) {
            MethodTree filterMethod = returnToMethod.get(tree);
            ExpressionTree retExpression = tree.getExpression();
            if (canBooleanExpressionEvalToTrue(retExpression)) {
                if (filterToNSMap.containsKey(filterMethod)) {
                    filterToNSMap.put(filterMethod, filterToNSMap.get(filterMethod).leastUpperBound(thenStore));
                } else {
                    filterToNSMap.put(filterMethod, thenStore);
                }
            }
        }
    }

    private static class StreamModelBuilder {

        private final List<StreamTypeRecord> typeRecords = new LinkedList<StreamTypeRecord>();
        private TypePredicate tp = null;
        private Set<String> filterMethodSigs;
        private Map<String, MaplikeMethodRecord> mapMethodSigToRecord;
        private Set<String> passthroughMethodSigs;

        private StreamModelBuilder() { }

        public static StreamModelBuilder start() {
            return new StreamModelBuilder();
        }

        public StreamModelBuilder addStreamType(TypePredicate tp) {
            if (this.tp != null) {
                typeRecords.add(
                        new StreamTypeRecord(
                                this.tp,
                                ImmutableSet.copyOf(filterMethodSigs),
                                ImmutableMap.copyOf(mapMethodSigToRecord),
                                ImmutableSet.copyOf(passthroughMethodSigs)));
            }
            this.tp = tp;
            this.filterMethodSigs = new HashSet<String>();
            this.mapMethodSigToRecord = new HashMap<String, MaplikeMethodRecord>();
            this.passthroughMethodSigs = new HashSet<String>();
            return this;
        }

        public StreamModelBuilder withFilterMethodFromSignature(String filterMethodSig) {
            this.filterMethodSigs.add(filterMethodSig);
            return this;
        }

        public StreamModelBuilder withMapMethodFromSignature(
                String methodSig,
                String innerMethodName,
                ImmutableSet<Integer> argsFromStream) {
            this.mapMethodSigToRecord.put(
                    methodSig,
                    new MaplikeMethodRecord(innerMethodName, argsFromStream));
            return this;
        }

        public StreamModelBuilder withPassthroughMethodFromSignature(String passthroughMethodSig) {
            this.passthroughMethodSigs.add(passthroughMethodSig);
            return this;
        }

        public ImmutableList<StreamTypeRecord> end() {
            if (this.tp != null) {
                typeRecords.add(
                        new StreamTypeRecord(
                                this.tp,
                                ImmutableSet.copyOf(filterMethodSigs),
                                ImmutableMap.copyOf(mapMethodSigToRecord),
                                ImmutableSet.copyOf(passthroughMethodSigs)));
            }
            return ImmutableList.copyOf(typeRecords);
        }
    }

    private static class StreamTypeRecord {

        private final TypePredicate typePredicate;

        // Names of all the methods of this type that behave like .filter(...) (must take exactly 1 argument)
        private final Set<String> filterMethodSigs;

        // Names and relevant arguments of all the methods of this type that behave like .map(...) for the
        // purposes of this checker (the listed arguments are those that take the potentially filtered objects from the
        // stream)
        private final Map<String, MaplikeMethodRecord> mapMethodSigToRecord;

        // List of methods of io.reactivex.Observable through which we just propagate the nullability information of the
        // last call, e.g. m() in Observable.filter(...).m().map(...) means the nullability information from filter(...)
        // should still be propagated to map(...), ignoring the interleaving call to m().
        // We assume that if m() is a pass-through method for Observable, so are m(a1), m(a1,a2), etc. If that is ever not
        // the case, we can use a more complex method subsignature her.
        private final Set<String> passthroughMethodSigs;

        public StreamTypeRecord(
                TypePredicate typePredicate,
                Set<String> filterMethodSigs,
                Map<String, MaplikeMethodRecord> mapMethodSigToRecord,
                Set<String> passthroughMethodSigs) {
            this.typePredicate = typePredicate;
            this.filterMethodSigs = filterMethodSigs;
            this.mapMethodSigToRecord = mapMethodSigToRecord;
            this.passthroughMethodSigs = passthroughMethodSigs;
        }

        public boolean matchesType(Type type, VisitorState state) {
            return typePredicate.apply(type, state);
        }

        public boolean isFilterMethod(String methodSig) {
            System.err.println(methodSig);
            return filterMethodSigs.contains(methodSig);
        }

        public boolean isMapMethod(String methodSig) {
            return mapMethodSigToRecord.containsKey(methodSig);
        }

        public MaplikeMethodRecord getMaplikeMethodRecord(String mapMethodSig) {
            return mapMethodSigToRecord.get(mapMethodSig);
        }

        public boolean isPassthroughMethod(String methodSig) {
            return passthroughMethodSigs.contains(methodSig);
        }

    }

    private static class MaplikeMethodRecord {

        private final String innerMethodName;
        public String getInnerMethodName() { return innerMethodName; }
        private final Set<Integer> argsFromStream;
        public Set<Integer> getArgsFromStream() { return argsFromStream; }

        public MaplikeMethodRecord(String innerMethodName, Set<Integer> argsFromStream) {
            this.innerMethodName = innerMethodName;
            this.argsFromStream = argsFromStream;
        }
    }

    private static class MaplikeToFilterInstanceRecord {

        private final MaplikeMethodRecord mapMR;
        public MaplikeMethodRecord getMaplikeMethodRecord() { return mapMR; }

        private final MethodTree filter;
        public MethodTree getFilter() { return filter; }

        public MaplikeToFilterInstanceRecord(MaplikeMethodRecord mapMR, MethodTree filter) {
            this.mapMR = mapMR;
            this.filter = filter;
        }

    }
}
