import java.util.*;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.*;
import org.eclipse.cdt.core.dom.ast.gnu.c.*;
import org.eclipse.cdt.core.parser.*;
import org.eclipse.cdt.internal.core.dom.parser.c.*;
import org.eclipse.cdt.internal.core.dom.parser.cpp.semantics.EvalUtil.*;

import com.laamella.sexpression.codec.*;
import com.laamella.sexpression.model.*;

import javaslang.collection.Vector;

class Util {

    static Expression mkAtom(String s, Type type) {
        return new Expression(Set.of(), new Atom(null, s.getBytes(), AtomCodec.SIMPLE, Vector.empty()), Set.of(), type);
    }

    static Expression mkAtom(TypedVar x) {
        return new Expression(Set.of(x), new Atom(null, x.name.getBytes(), AtomCodec.SIMPLE, Vector.empty()), Set.of(), x.type);
    }

    static Expression mkNondet(TypedVar x) {
        return new Expression(Set.of(), new Atom(null, x.name.getBytes(), AtomCodec.SIMPLE, Vector.empty()), Set.of(x), x.type);
    }

    static Expression mkAtomList(Type type, Expression... atoms) {
        Set<TypedVar> vars = new LinkedHashSet<>();
        Set<TypedVar> nondet = new LinkedHashSet<>();
        ArrayList<SExpression> as = new ArrayList<>();
        for (var a: atoms) {
            vars.addAll(a.allVars());
            as.add(a.ex);
        }
        return new Expression(vars, new AtomList(null, Vector.ofAll(as), Vector.empty()), nondet, type);
    }
}

enum BaseType {
    Bool, Int, Void;
}

class Type {

    BaseType type;
    int dim;

    public Type(BaseType type, int dim) {
        this.type = type;
        this.dim = dim;
    }

    @Override
    public String toString() {
        var res = new StringBuilder();
        for (int i = 0; i < dim; ++i) {
            res.append("(Array Int ");
        }
        res.append(type);
        for (int i = 0; i < dim; ++i) {
            res.append(")");
        }
        return res.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(dim, type);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Type other = (Type) obj;
        return dim == other.dim && type == other.type;
    }

    static Type Int = new Type(BaseType.Int, 0);
    static Type Bool = new Type(BaseType.Bool, 0);
    static Type Void = new Type(BaseType.Void, 0);

}

class TypedVar {

    Type type;
    String name;
    Optional<Expression> initializer;

    public TypedVar(Type type, String name, Optional<Expression> initializer) {
        this.type = type;
        if (name.startsWith("|")) {
            this.name = name;
        } else {
            this.name = "|" + name + "|";
        }
        this.initializer = initializer;
    }

    @Override
    public String toString() {
        return name + ": " + type;
    }

    @Override
    public int hashCode() {
        return Objects.hash(name, type);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        TypedVar other = (TypedVar) obj;
        return Objects.equals(name, other.name) && Objects.equals(type, other.type);
    }

}

class Scope {

    private Map<String, BaseType> undefined = new LinkedHashMap<>();
    ArrayList<LinkedHashMap<String, TypedVar>> vars = new ArrayList<>();
    private ArrayList<IASTFileLocation> context = new ArrayList<>();
    private Map<String, Expression> enums = new LinkedHashMap<>();
    private Map<String, BaseType> typedefs = new LinkedHashMap<>();
    private static String retVarName = "__HORN_KLAUS_return";

    Scope() {
        vars.add(new LinkedHashMap<>());
        addVar(retVarName, Type.Int, Optional.empty());
    }

    void push() {
        vars.add(new LinkedHashMap<>());
    }

    boolean pop() {
        var res = !vars.getLast().isEmpty();
        vars.removeLast();
        return res;
    }

    void execCall(IASTFileLocation loc) {
        context.add(loc);
    }

    void execReturn() {
        context.removeLast();
    }

    Optional<TypedVar> getVar(String name) {
        for (var map : vars.reversed()) {
            if (map.containsKey(name)) {
                return Optional.of(map.get(name));
            }
        }
        return Optional.empty();
    }

    TypedVar getReturnVar() {
        return getVar(retVarName).get();
    }

    Optional<BaseType> isUndefined(String name) {
        return Optional.ofNullable(undefined.get(name));
    }

    TypedVar addVar(String name, Type type, Optional<Expression> initializer) {
        String fullName;
        if (getVar(name).isPresent()) {
            int level = vars.size();
            fullName = name + ":" + level;
        } else {
            fullName = name;
        }
        var res = new TypedVar(type, fullName, initializer);
        vars.getLast().put(name, res);
        return res;
    }

    void addUndefinedFunction(String name, BaseType type) {
        undefined.put(name, type);
    }

    ArrayList<Type> signature() {
        ArrayList<Type> res = new ArrayList<>();
        for (var map: vars) {
            for (var e: map.entrySet()) {
                res.add(e.getValue().type);
            }
        }
        return res;
    }

    ArrayList<TypedVar> getVars() {
        ArrayList<TypedVar> res = new ArrayList<>();
        for (var map: vars) {
            res.addAll(map.values());
        }
        return res;
    }

    ArrayList<IASTFileLocation> getContext() {
        return context;
    }

    void addEnumValue(String name, Expression val) {
        enums.put(name, val);
    }

    Optional<Expression> getEnumVal(String name) {
        return Optional.ofNullable(enums.get(name));
    }

    void addTypedef(String name, BaseType val) {
        typedefs.put(name, val);
    }

    Optional<BaseType> getTypedef(String name) {
        return Optional.ofNullable(typedefs.get(name));
    }

}

class FunctionSymbol {

    public FunctionSymbol(String name, List<Type> type) {
        if (name.startsWith("|")) {
            this.name = name;
        } else {
            this.name = "|" + name + "|";
        }
        this.type = type;
    }

    String name;
    List<Type> type;

    @Override
    public String toString() {
        return name;
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        FunctionSymbol other = (FunctionSymbol) obj;
        return Objects.equals(name, other.name);
    }

}

class FunApp {

    public FunApp(FunctionSymbol f, List<Expression> args) {
        this.f = f;
        this.args = args;
    }

    FunctionSymbol f;
    List<Expression> args;

    @Override
    public String toString() {
        if (args.isEmpty()) {
            return f.toString();
        }
        var res = new StringBuilder();
        res.append("(");
        res.append(f);
        for (var arg: args) {
            res.append(" ");
            res.append(arg);
        }
        res.append(")");
        return res.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(args, f);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        FunApp other = (FunApp) obj;
        return Objects.equals(args, other.args) && Objects.equals(f, other.f);
    }

    Set<TypedVar> allVars() {
        Set<TypedVar> res = new LinkedHashSet<>();
        for (var arg: args) {
            res.addAll(arg.allVars());
        }
        return res;
    }

}

class Clause {

    public Clause(FunApp premise, Expression constraint, FunApp conclusion) {
        this.premise = premise;
        this.constraint = constraint;
        this.conclusion = conclusion;
    }

    FunApp premise;
    Expression constraint;
    FunApp conclusion;

    public String toSexp() {
        Set<TypedVar> vars = new LinkedHashSet<>();
        vars.addAll(premise.allVars());
        vars.addAll(constraint.allVars());
        vars.addAll(conclusion.allVars());
        var res = new StringBuilder();
        if (!vars.isEmpty()) {
            res.append("(forall (");
            for (var x: vars) {
                res.append("\n  (");
                res.append(x.name);
                res.append(" ");
                res.append(x.type);
                res.append(")");
            }
            res.append(")\n");
        }
        if (constraint.equals(Expression.True)) {
            res.append("(=>\n  ");
            res.append(premise);
            res.append("\n  ");
            res.append(conclusion);
            res.append(")");
        } else {
            res.append("(=> (and\n  ");
            res.append(premise);
            res.append("\n  ");
            res.append(constraint);
            res.append(")\n  ");
            res.append(conclusion);
            res.append(")");
        }
        if (!vars.isEmpty()) {
            res.append(")");
        }
        return res.toString();
    }

    public String toAri() {
        var res = new StringBuilder();
        res.append("(rule ");
        res.append(premise);
        res.append(" ");
        res.append(conclusion);
        if (!constraint.equals(Expression.True)) {
            res.append(" :guard ");
            res.append(constraint);
        }
        res.append(")\n");
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        if (!constraint.equals(Expression.True)) {
            res.append("if ");
            res.append(constraint.toString());
            res.append(":\n");
        }
        res.append(premise.f);
        res.append("\n");
        int arr = Math.min(premise.args.size(), conclusion.args.size());
        for (int i = 0; i < arr; ++i) {
            if (!premise.args.get(i).equals(conclusion.args.get(i))) {
                res.append("    ");
                res.append(premise.args.get(i));
                res.append(" := ");
                res.append(conclusion.args.get(i));
                res.append("\n");
            }
        }
        res.append(conclusion.f);
        res.append("\n");
        return res.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(conclusion, constraint, premise);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Clause other = (Clause) obj;
        return Objects.equals(conclusion, other.conclusion) && Objects.equals(constraint, other.constraint)
                && Objects.equals(premise, other.premise);
    }

}

class Flow {

    public Flow(FunctionSymbol normalFlow) {
        this.normalFlow = Optional.of(normalFlow);
        returnFlow.add(new LinkedHashMap<>());
    }

    ArrayList<Set<FunApp>> breakFlow = new ArrayList<>();
    ArrayList<Set<FunApp>> continueFlow = new ArrayList<>();
    ArrayList<Map<FunApp, Optional<Expression>>> returnFlow = new ArrayList<>();
    Optional<FunctionSymbol> normalFlow;

    void setFlow(FunctionSymbol normalFlow) {
        this.normalFlow = Optional.of(normalFlow);
    }

    void execCall() {
        returnFlow.add(new LinkedHashMap<>());
    }

    void execReturn() {
        returnFlow.removeLast();
    }

    void enterLoop() {
        breakFlow.add(new LinkedHashSet<>());
        continueFlow.add(new LinkedHashSet<>());
    }

    void exitLoop() {
        breakFlow.removeLast();
        continueFlow.removeLast();
    }

}

class Expression {

    public Expression(Set<TypedVar> vars, SExpression ex, Set<TypedVar> nondet, Type type) {
        this.vars = vars;
        this.ex = ex;
        this.nondet = nondet;
        this.type = type;
    }

    static Expression True = Util.mkAtom("true", Type.Bool);

    Set<TypedVar> vars;
    Set<TypedVar> nondet;
    SExpression ex;
    Type type;

    @Override
    public String toString() {
        return ex.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(ex.toString(), vars);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Expression other = (Expression) obj;
        return Objects.equals(ex.toString(), other.ex.toString()) && Objects.equals(vars, other.vars);
    }

    Expression toBool() {
        if (type.equals(Type.Bool)) {
            return this;
        }
        if (type.dim > 0) {
            throw new IllegalArgumentException("cannot convert array to bool");
        }
        return Util.mkAtomList(Type.Bool, Util.mkAtom("distinct", Type.Void), this, Util.mkAtom("0", Type.Int));
    }

    Expression toInt() {
        if (type.equals(Type.Int)) {
            return this;
        }
        if (type.dim > 0) {
            throw new IllegalArgumentException("cannot convert array to int");
        }
        return Util.mkAtomList(Type.Int, Util.mkAtom("ite", Type.Void), this, Util.mkAtom("1", Type.Int), Util.mkAtom("0", Type.Int));
    }

    Set<TypedVar> allVars() {
        Set<TypedVar> res = new LinkedHashSet<>();
        res.addAll(vars);
        res.addAll(nondet);
        return res;
    }

    public Expression toType(Type type) {
        if (this.type.equals(type)) {
            return this;
        }
        if (type.equals(Type.Bool)) {
            return toBool();
        }
        if (type.equals(Type.Int)) {
            return toInt();
        }
        throw new IllegalArgumentException("cannot convert to " + type);
    }

}

class CHCs {

    private Set<Clause> clauses = new LinkedHashSet<>();
    private FunApp fact;
    private Set<Pair<FunApp, Expression>> queries = new LinkedHashSet<>();

    CHCs(FunApp fact) {
        this.fact = fact;
    }

    void addClause(FunApp lhs, Expression cond, FunApp rhs) {
        clauses.add(new Clause(lhs, cond, rhs));
    }

    void addQuery(FunApp lhs, Expression cond) {
        queries.add(new Pair<>(lhs, cond));
    }

    public String toSexp() {
        var res = new StringBuilder();
        res.append("(set-logic HORN)\n");
        Set<FunctionSymbol> predicates = new LinkedHashSet<>();
        predicates.add(fact.f);
        for (var c: clauses) {
            predicates.add(c.premise.f);
            predicates.add(c.conclusion.f);
        }
        for (var q: queries) {
            predicates.add(q.getFirst().f);
        }
        for (var p: predicates) {
            res.append("(declare-fun ");
            res.append(p);
            res.append(" (");
            for (var t: p.type) {
                res.append(t);
                res.append(" ");
            }
            res.append(") Bool)\n");
        }
        var trueSym = new FunApp(new FunctionSymbol("true", List.of()), List.of());
        var falseSym = new FunApp(new FunctionSymbol("false", List.of()), List.of());
        res.append("(assert ");
        res.append(new Clause(trueSym, Expression.True, fact).toSexp());
        res.append(")\n");
        for (var c: clauses) {
            res.append("(assert ");
            res.append(c.toSexp());
            res.append(")\n");
        }
        for (var q: queries) {
            res.append("(assert ");
            res.append(new Clause(q.getFirst(), q.getSecond(), falseSym).toSexp());
            res.append(")\n");
        }
        res.append("(check-sat)\n");
        return res.toString();
    }

    public String toAri() {
        var res = new StringBuilder();
        res.append("(format LCTRS)\n");
        res.append("(theory Ints)\n");
        Set<FunctionSymbol> predicates = new LinkedHashSet<>();
        predicates.add(fact.f);
        for (var c: clauses) {
            predicates.add(c.premise.f);
            predicates.add(c.conclusion.f);
        }
        for (var q: queries) {
            predicates.add(q.getFirst().f);
        }
        for (var p: predicates) {
            res.append("(fun ");
            res.append(p);
            res.append(" (-> ");
            for (var t: p.type) {
                res.append(t);
                res.append(" ");
            }
            res.append("Int))\n");
        }
        res.append("(entrypoint ");
        res.append(fact.f);
        res.append(")\n");
        for (var c: clauses) {
            res.append(c.toAri());
        }
        return res.toString();
    }

}

public class HornClaus {

    private Scope scope = new Scope();
    private Map<String, IASTFunctionDefinition> functions = new LinkedHashMap<>();
    private CHCs chcs;

    public static boolean ari;
    public static String delimiter = ":";
    public static String filename;
    public static boolean invert = false;

    HornClaus(FunctionSymbol startFlow) {
        chcs = new CHCs(mkFunApp(startFlow));
    }

    Expression parseArrayRead(IASTArraySubscriptExpression arraySubscriptExpression, Flow flow) {
        var array = parseExpression(arraySubscriptExpression.getArrayExpression(), flow);
        var arg = switch (arraySubscriptExpression.getArgument()) {
            case IASTExpression i -> parseExpression(i, flow);
            default -> throw new IllegalArgumentException("unsupported array subscript: " + arraySubscriptExpression.getArgument().getRawSignature());
        };
        Type type = new Type(array.type.type, array.type.dim - 1);
        return Util.mkAtomList(type, Util.mkAtom("select", Type.Void), array, arg);
    }

    void update(Flow flow, FunApp lhs, Expression cond, FunApp rhs) {
        flow.setFlow(rhs.f);
        chcs.addClause(lhs, cond, rhs);
    }

    void update(Flow flow, FunApp lhs, FunApp rhs) {
        update(flow, lhs, Expression.True, rhs);
    }

    void addClauses(Collection<FunApp> lhss, FunApp rhs) {
        for (var lhs: lhss) {
            chcs.addClause(lhs, Expression.True, rhs);
        }
    }

    Expression parseVariableAssignent(IASTIdExpression lhsEx, Expression second, Flow flow) {
        var preFlow = flow.normalFlow.get();
        var lhs = mkFunApp(preFlow);
        var x = scope.getVar(lhsEx.getName().toString()).get();
        var rhs = mkFunApp("assign", lhsEx.getFileLocation(), Map.of(x,  second));
        update(flow, lhs, rhs);
        return second;
    }

    Expression parseArrayAssignment(IASTArraySubscriptExpression lhsEx, Expression second, Flow flow) {
        var preFlow = flow.normalFlow.get();
        var lhs = mkFunApp(preFlow);
        TypedVar arrayVar = switch (lhsEx.getArrayExpression()) {
            case IASTIdExpression arrId -> scope.getVar(arrId.getName().toString()).get();
            default -> throw new IllegalArgumentException("unsupported assignment to: " + lhsEx.getRawSignature());
        };
        var array = Util.mkAtom(arrayVar);
        var arg = switch (lhsEx.getArgument()) {
            case IASTExpression i -> parseExpression(i, flow);
            default -> throw new IllegalArgumentException("unsupported array subscript: " + lhsEx.getArgument().getRawSignature());
        };
        var store = Util.mkAtomList(array.type, Util.mkAtom("store", Type.Void), array, arg, second);
        var rhs = mkFunApp("assign", lhsEx.getFileLocation(), Map.of(arrayVar, store));
        update(flow, lhs, rhs);
        return second;
    }

    Expression parseAssignment(IASTBinaryExpression assignment, Expression second, Flow flow) {
        switch (assignment.getOperand1()) {
            case IASTIdExpression idExpression -> {
                return parseVariableAssignent(idExpression, second, flow);
            }
            case IASTArraySubscriptExpression arraySubscriptExpression -> {
                return parseArrayAssignment(arraySubscriptExpression, second, flow);
            }
            default -> throw new IllegalArgumentException("unsupported assignment: " + assignment.getRawSignature());
        }
    }

    Expression mkBinaryOp(String op, Expression first, Expression second, Type type) {
        return Util.mkAtomList(type, Util.mkAtom(op, Type.Void), first, second);
    }

    Expression parseBinaryExpression(IASTBinaryExpression binaryExpression, Flow flow) {
        var first = parseExpression(binaryExpression.getOperand1(), flow);
        var second = parseExpression(binaryExpression.getOperand2(), flow);
        switch (binaryExpression.getOperator()) {
            case IASTBinaryExpression.op_assign -> {
                return parseAssignment(binaryExpression, second, flow);
            }
            case IASTBinaryExpression.op_logicalAnd -> {
                // TODO shortcut semantics
                return mkBinaryOp("and", first.toBool(), second.toBool(), Type.Bool);
            }
            case IASTBinaryExpression.op_logicalOr -> {
                // TODO shortcut semantics
                return mkBinaryOp("or", first.toBool(), second.toBool(), Type.Bool);
            }
            case IASTBinaryExpression.op_equals -> {
                return mkBinaryOp("=", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_greaterEqual -> {
                return mkBinaryOp(">=", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_greaterThan -> {
                return mkBinaryOp(">", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_lessEqual -> {
                return mkBinaryOp("<=", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_lessThan -> {
                return mkBinaryOp("<", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_minus -> {
                return mkBinaryOp("-", first, second, Type.Int);
            }
            case IASTBinaryExpression.op_minusAssign -> {
                second = mkBinaryOp("-", first, second, Type.Int);
                return parseAssignment(binaryExpression, second, flow);
            }
            case IASTBinaryExpression.op_multiply -> {
                return mkBinaryOp("*", first, second, Type.Int);
            }
            case IASTBinaryExpression.op_multiplyAssign -> {
                second = mkBinaryOp("*", first, second, Type.Int);
                return parseAssignment(binaryExpression, second, flow);
            }
            case IASTBinaryExpression.op_notequals -> {
                return mkBinaryOp("distinct", first, second, Type.Bool);
            }
            case IASTBinaryExpression.op_plus -> {
                return mkBinaryOp("+", first, second, Type.Int);
            }
            case IASTBinaryExpression.op_plusAssign -> {
                second = mkBinaryOp("+", first, second, Type.Int);
                return parseAssignment(binaryExpression, second, flow);
            }
            case IASTBinaryExpression.op_modulo -> {
                return mkBinaryOp("mod", first, second, Type.Int);
            }
            case IASTBinaryExpression.op_divide -> {
                return mkBinaryOp("div", first, second, Type.Int);
            }
            default -> throw new IllegalArgumentException("unsupported binary expression: " + binaryExpression.getRawSignature());
        }
    }

    Expression parseConditional(IASTConditionalExpression conditional, Flow flow) {
        var preFlow = flow.normalFlow.get();
        var cond = parseExpression(conditional.getLogicalConditionExpression(), flow).toBool();
        var lhs = mkFunApp(preFlow);
        var exitFlow = mkFunctionSymbol("cond_exit", conditional.getFileLocation());
        var then = mkFunApp("cond_then", conditional.getFileLocation());
        var elseApp = mkFunApp("cond_else", conditional.getFileLocation());
        update(flow, lhs, cond, then);
        var pos = parseExpression(conditional.getPositiveResultExpression(), flow);
        if (flow.normalFlow.isPresent()) {
            var postThenFlow = flow.normalFlow.get();
            update(flow, mkFunApp(postThenFlow), mkFunApp(exitFlow));
        }
        flow.setFlow(preFlow);
        update(flow, lhs, negate(cond), elseApp);
        var neg = parseExpression(conditional.getNegativeResultExpression(), flow);
        if (flow.normalFlow.isPresent()) {
            var postElseFlow = flow.normalFlow.get();
            update(flow, mkFunApp(postElseFlow), mkFunApp(exitFlow));
        }
        flow.setFlow(exitFlow);
        return Util.mkAtomList(pos.type, Util.mkAtom("ite", Type.Void), cond, pos, neg);
    }

    Expression parseFunctionCall(IASTFunctionCallExpression functionCallExpression, Flow flow) {
        flow.execCall();
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        switch (functionCallExpression.getFunctionNameExpression()) {
            case IASTIdExpression idExpression -> {
                var name = idExpression.getName().toString();
                if (name.equals("__VERIFIER_assert")) {
                    assert(functionCallExpression.getArguments().length == 1);
                    var argEx = functionCallExpression.getArguments()[0];
                    switch (argEx) {
                        case IASTExpression ex -> {
                            var arg = parseExpression(ex, flow).toBool();
                            chcs.addQuery(mkFunApp(preFlow), invert ? arg : negate(arg));
                            var postFlow = mkFunctionSymbol("postAssert", functionCallExpression.getFileLocation());
                            update(flow, mkFunApp(preFlow), arg, mkFunApp(postFlow));
                            return Expression.True;
                        }
                        default -> throw new IllegalArgumentException("unsupported argument: " + argEx.getRawSignature());
                    }
                }
                if (name.equals("abort")) {
                    flow.normalFlow = Optional.empty();
                    return Expression.True;
                }
                var undefined = scope.isUndefined(name);
                if (undefined.isPresent()) {
                    if (!name.startsWith("__VERIFIER_nondet")) {
                        throw new IllegalArgumentException("unknown undefined function " + name);
                    }
                    if (undefined.get() != BaseType.Void) {
                        return Util.mkNondet(new TypedVar(new Type(undefined.get(), 0), name, Optional.empty()));
                    } else {
                        return Expression.True;
                    }
                }
                var fun = functions.get(name);
                var returnType = parseDeclSpecifier(fun.getDeclSpecifier());
                ArrayList<Expression> actualArgs = new ArrayList<>();
                for (var init: functionCallExpression.getArguments()) {
                    switch (init) {
                        case IASTExpression ex -> {
                            actualArgs.add(parseExpression(ex, flow));
                        }
                        default -> throw new IllegalArgumentException("unsupported function argument: " + init.getRawSignature());
                    }

                }
                scope.execCall(functionCallExpression.getFileLocation());
                scope.push();
                int i = 0;
                Map<TypedVar, Expression> args = new LinkedHashMap<>();
                switch (fun.getDeclarator()) {
                    case IASTStandardFunctionDeclarator functionDeclarator -> {
                        for (var param: functionDeclarator.getParameters()) {
                            var type = parseDeclSpecifier(param.getDeclSpecifier());
                            var arg = parseDeclarator(param.getDeclarator(), type, flow).get();
                            args.put(arg, actualArgs.get(i).toType(arg.type));
                            ++i;
                        }
                    }
                    default -> throw new IllegalArgumentException("unsupported function declarator: " + fun.getDeclarator().getRawSignature());
                }

                var postInitFlow = flow.normalFlow.get();
                if (i > 0) {
                    var callFlow = mkFunctionSymbol("call", functionCallExpression.getFileLocation());
                    update(flow, mkFunApp(postInitFlow), mkFunApp(callFlow, args));
                }
                parseStatement(fun.getBody(), flow);
                Map<FunApp, Optional<Expression>> returns = new LinkedHashMap<>();
                for (var e: flow.returnFlow.getLast().entrySet()) {
                    returns.put(e.getKey(), e.getValue());
                }
                if (flow.normalFlow.isPresent()) {
                    returns.put(mkFunApp(flow.normalFlow.get()), Optional.empty());
                }
                scope.pop();
                scope.execReturn();
                var ret = mkFunctionSymbol(name + "_return", functionCallExpression.getFileLocation());
                var rhs = mkFunApp(ret);
                for (var e : returns.entrySet()) {
                    FunApp retRhs = switch (returnType) {
                        case BaseType.Void -> rhs;
                        case BaseType.Int -> mkFunApp(ret, Map.of(scope.getReturnVar(), e.getValue().get()));
                        case BaseType.Bool -> mkFunApp(ret, Map.of(scope.getReturnVar(), e.getValue().get().toInt()));
                    };
                    chcs.addClause(e.getKey(), Expression.True, retRhs);
                }
                flow.setFlow(ret);
                flow.execReturn();
                return Util.mkAtom(scope.getReturnVar());
            }
            default -> throw new IllegalArgumentException("unsupoprted function call: " + functionCallExpression.getRawSignature());
        }
    }

    Pair<Expression, Expression> parsePrePostFixOp(IASTUnaryExpression expression, Flow flow, String op) {
        var arg = parseExpression(expression.getOperand(), flow);
        var updated = Util.mkAtomList(Type.Int, Util.mkAtom(op, Type.Void), arg, Util.mkAtom("1", Type.Int));
        TypedVar x;
        switch (expression.getOperand()) {
            case IASTIdExpression idExpression -> {
                x = scope.getVar(idExpression.getName().toString()).get();
            }
            case IASTArraySubscriptExpression subscriptExpression -> {
                switch (subscriptExpression.getArgument()) {
                    case IASTIdExpression idExpression -> {
                        x = scope.getVar(idExpression.getName().toString()).get();
                        updated = parseArrayAssignment(subscriptExpression, updated, flow);
                    }
                    default -> throw new IllegalArgumentException("unsupported postfix-op: " + expression.getRawSignature());
                }
            }
            default -> throw new IllegalArgumentException("invalid postfix-op: " + expression.getRawSignature());
        }
        var preFlow = flow.normalFlow.get();
        var lhs = mkFunApp(preFlow);
        var rhs = mkFunApp("pre_or_postfix", expression.getFileLocation(), Map.of(x, updated));
        update(flow, lhs, rhs);
        return new Pair<>(arg, updated);
    }

    Expression parseLiteral(IASTLiteralExpression literalExpression) {
        switch (literalExpression.getKind()) {
            case IASTLiteralExpression.lk_false -> {
                return Util.mkAtom("false", Type.Bool);
            }
            case IASTLiteralExpression.lk_true -> {
                return Util.mkAtom("true", Type.Bool);
            }
            case IASTLiteralExpression.lk_integer_constant -> {
                return Util.mkAtom(new String(literalExpression.getValue()), Type.Int);
            }
            default -> throw new IllegalArgumentException("unsupported literal " + literalExpression.getRawSignature());
        }
    }

    Expression parseExpression(IASTExpression expression, Flow flow) {
        switch (expression) {
            case IASTArraySubscriptExpression arraySubscriptExpression -> {
                return parseArrayRead(arraySubscriptExpression, flow);
            }
            case IASTBinaryExpression binaryExpression -> {
                return parseBinaryExpression(binaryExpression, flow);
            }
            case IASTCastExpression castExpression -> {
                return parseExpression(castExpression.getOperand(), flow);
            }
            case IASTConditionalExpression conditionalExpression -> {
                return parseConditional(conditionalExpression, flow);
            }
            case IASTExpressionList expressionList -> {
                Expression res = Expression.True;
                for (var e: expressionList.getExpressions()) {
                    res = parseExpression(e, flow);
                }
                return res;
            }
            case IASTFunctionCallExpression functionCallExpression -> {
                return parseFunctionCall(functionCallExpression, flow);
            }
            case IASTIdExpression idExpression -> {
                var name = idExpression.getName().toString();
                var varRes = scope.getVar(name);
                if (varRes.isPresent()) {
                    return Util.mkAtom(varRes.get());
                }
                var enumRes = scope.getEnumVal(name);
                if (enumRes.isPresent()) {
                    return enumRes.get();
                }
                throw new IllegalArgumentException(idExpression.getFileLocation().getStartingLineNumber() + ":" + idExpression.getFileLocation().getNodeOffset());
            }
            case IASTLiteralExpression literalExpression -> {
                return parseLiteral(literalExpression);
            }
            case IASTUnaryExpression unaryExpression -> {
                var arg = parseExpression(unaryExpression.getOperand(), flow);
                switch (unaryExpression.getOperator()) {
                    case IASTUnaryExpression.op_minus -> {
                        return Util.mkAtomList(Type.Int, Util.mkAtom("-", Type.Void), arg);
                    }
                    case IASTUnaryExpression.op_not -> {
                        return negate(arg);
                    }
                    case IASTUnaryExpression.op_plus -> {
                        return arg;
                    }
                    case IASTUnaryExpression.op_postFixDecr -> {
                        return parsePrePostFixOp(unaryExpression, flow, "-").getFirst();
                    }
                    case IASTUnaryExpression.op_postFixIncr -> {
                        return parsePrePostFixOp(unaryExpression, flow, "+").getFirst();
                    }
                    case IASTUnaryExpression.op_prefixDecr -> {
                        return parsePrePostFixOp(unaryExpression, flow, "-").getSecond();
                    }
                    case IASTUnaryExpression.op_prefixIncr -> {
                        return parsePrePostFixOp(unaryExpression, flow, "+").getSecond();
                    }
                    case IASTUnaryExpression.op_bracketedPrimary -> {
                        return parseExpression(unaryExpression.getOperand(), flow);
                    }
                    default -> throw new IllegalArgumentException("unsupported unary expression: " + unaryExpression.getRawSignature());
                }
            }
            default -> throw new IllegalArgumentException("unsupported expression: " + expression.getRawSignature());
        }
    }

    Expression negate(Expression ex) {
        return Util.mkAtomList(Type.Bool, Util.mkAtom("not", Type.Void), ex.toBool());
    }

    void parseDeclarators(IASTDeclarator[] declarators, BaseType type, Flow flow) {
        for (var d: declarators) {
            parseDeclarator(d, type, flow);
        }
    }

    Optional<TypedVar> parseDeclarator(IASTDeclarator declarator, BaseType type, Flow flow) {
        if (declarator.getPointerOperators().length > 0) {
            throw new IllegalArgumentException("unsupported pointer declarator: " + declarator);
        }
        var preFlow = flow.normalFlow.get();
        var lhs = mkFunApp(preFlow);
        String name = declarator.getName().toString();
        int dim;
        switch (declarator) {
            case IASTStandardFunctionDeclarator functionDeclarator -> {
                scope.addUndefinedFunction(name, type);
                return Optional.empty();
            }
            case IASTArrayDeclarator arrayDeclarator -> dim = arrayDeclarator.getArrayModifiers().length;
            case CASTDeclarator cDeclarator -> dim = 0;
            default -> throw new IllegalArgumentException("unsupported declarator: " + declarator.getRawSignature());
        }
        Optional<Expression> initializer = Optional.empty();
        switch (declarator.getInitializer()) {
            case null -> {}
            case IASTEqualsInitializer equalsInitializer -> {
                switch (equalsInitializer.getInitializerClause()) {
                    case IASTExpression exp -> initializer = Optional.of(parseExpression(exp, flow));
                    default -> throw new IllegalArgumentException("unsupported initializer: " + equalsInitializer.getRawSignature());
                }
            }
            default -> throw new IllegalArgumentException("unsupported initializer: " + declarator.getInitializer());
        }
        var x = scope.addVar(name, new Type(type, dim), initializer);
        Map<TypedVar, Expression> init = initializer.map(y -> Map.of(x, y)).orElse(Map.of());
        var rhs = mkFunApp("init", declarator.getFileLocation(), init);
        update(flow, lhs, rhs);
        return Optional.of(x);
    }

    BaseType parseDeclSpecifier(IASTDeclSpecifier specifier) {
        return switch (specifier) {
            case IASTSimpleDeclSpecifier spec -> switch (spec.getType()) {
                case IASTSimpleDeclSpecifier.t_bool -> BaseType.Bool;
                case IASTSimpleDeclSpecifier.t_int -> BaseType.Int;
                case IASTSimpleDeclSpecifier.t_void -> BaseType.Void;
                case IASTSimpleDeclSpecifier.t_unspecified -> BaseType.Int;
                default -> throw new IllegalArgumentException("unsupported type: " + spec.getRawSignature());
            };
            case IASTNamedTypeSpecifier spec -> {
                var type = scope.getTypedef(spec.getName().toString());
                if (type.isPresent()) {
                    yield type.get();
                }
                throw new IllegalArgumentException("unknown type " + type);
            }
            case IASTEnumerationSpecifier spec -> {
                int count = 0;
                for (var e : spec.getEnumerators()) {
                    Expression value;
                    value = switch (e.getValue()) {
                        case null -> Util.mkAtom(Integer.toString(count), Type.Int);
                        case IASTLiteralExpression lit -> {
                            count = Integer.parseInt(new String(lit.getValue()));
                            yield parseLiteral(lit);
                        }
                        default -> throw new IllegalArgumentException("enum with non-literal value");
                    };
                    scope.addEnumValue(e.getName().toString(), value);
                    ++count;
                }
                yield BaseType.Int;
            }
            default -> throw new IllegalArgumentException("unsupported specifier: " + specifier.getRawSignature());
        };
    }

    FunApp mkFunApp(FunctionSymbol f, Map<TypedVar, Expression> subs) {
        var lhsVars = scope.getVars();
        ArrayList<Expression> lhsArgs = new ArrayList<>();
        List<Type> signature = new ArrayList<>();
        for (var x: lhsVars) {
            if (subs.containsKey(x)) {
                lhsArgs.add(subs.get(x));
            } else {
                lhsArgs.add(Util.mkAtom(x));
            }
            signature.add(x.type);
        }
        if (!signature.equals(f.type)) {
            System.err.println(lhsVars);
            throw new IllegalArgumentException("type mismatch for " + f + "; expected: " + f.type + "; actual: " + signature);
        }
        var lhs = new FunApp(f, lhsArgs);
        return lhs;
    }

    FunApp mkFunApp(FunctionSymbol f) {
        return mkFunApp(f, Map.of());
    }

    FunApp mkFunApp(String name, IASTFileLocation loc) {
        return mkFunApp(mkFunctionSymbol(name, loc));
    }

    FunApp mkFunApp(String name, IASTFileLocation loc, Map<TypedVar, Expression> subs) {
        return mkFunApp(mkFunctionSymbol(name, loc), subs);
    }

    void parseTypedef(IASTSimpleDeclaration declaration) {
        var type = parseDeclSpecifier(declaration.getDeclSpecifier());
        var declarators = declaration.getDeclarators();
        if (declarators.length != 1) {
            throw new IllegalArgumentException("a typedef must have one and only one declarator");
        }
        var id = declarators[0].getName().toString();
        scope.addTypedef(id, type);
    }

    void parseDeclaration(IASTSimpleDeclaration declaration, Flow flow) {
        var type = parseDeclSpecifier(declaration.getDeclSpecifier());
        parseDeclarators(declaration.getDeclarators(), type, flow);
    }

    void parseDo(IASTDoStatement doStatement, Flow flow) {
        flow.enterLoop();
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        scope.push();
        parseStatement(doStatement.getBody(), flow);
        ArrayList<FunApp> continues = new ArrayList<>(flow.continueFlow.getLast());
        ArrayList<FunApp> breaks = new ArrayList<>(flow.breakFlow.getLast());
        if (flow.normalFlow.isPresent()) {
            continues.add(mkFunApp(flow.normalFlow.get()));
        }
        scope.pop();
        var beforeCheckFlow = mkFunctionSymbol("do_check", doStatement.getFileLocation());
        var beforeCheck = mkFunApp(beforeCheckFlow);
        addClauses(continues, beforeCheck);
        flow.setFlow(beforeCheckFlow);
        var cond = parseExpression(doStatement.getCondition(), flow).toBool();
        var afterCheckFlow = flow.normalFlow.get();
        var afterCheck = mkFunApp(afterCheckFlow);
        chcs.addClause(afterCheck, cond, pre);
        var exitFlow = mkFunctionSymbol("do_exit", doStatement.getFileLocation());
        var exit = mkFunApp(exitFlow);
        addClauses(breaks, exit);
        update(flow, afterCheck, negate(cond), exit);
        flow.exitLoop();
    }

    void parseWhile(IASTWhileStatement whileStatement, Flow flow) {
        flow.enterLoop();
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        var cond = parseExpression(whileStatement.getCondition(), flow).toBool();
        var afterCheckFlow = flow.normalFlow.get();
        var afterCheck = mkFunApp(afterCheckFlow);
        var enterFlow = mkFunctionSymbol("while_enter", whileStatement.getFileLocation());
        var enter = mkFunApp(enterFlow);
        update(flow, afterCheck, cond, enter);
        scope.push();
        parseStatement(whileStatement.getBody(), flow);
        ArrayList<FunApp> continues = new ArrayList<>(flow.continueFlow.getLast());
        ArrayList<FunApp> breaks = new ArrayList<>(flow.breakFlow.getLast());
        if (flow.normalFlow != null) {
            continues.add(mkFunApp(flow.normalFlow.get()));
        }
        scope.pop();
        addClauses(continues, pre);
        var exitFlow = mkFunctionSymbol("while_exit", whileStatement.getFileLocation());
        var exit = mkFunApp(exitFlow);
        addClauses(breaks, exit);
        update(flow, afterCheck, negate(cond), exit);
        flow.exitLoop();
    }

    void parseFor(IASTForStatement forStatement, Flow flow) {
        scope.push();
        parseStatement(forStatement.getInitializerStatement(), flow);
        flow.enterLoop();
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        var cond = parseExpression(forStatement.getConditionExpression(), flow).toBool();
        var afterCheckFlow = flow.normalFlow.get();
        var afterCheck = mkFunApp(afterCheckFlow);
        var enterFlow = mkFunctionSymbol("for_enter", forStatement.getFileLocation());
        var enter = mkFunApp(enterFlow);
        update(flow, afterCheck, cond, enter);
        scope.push();
        parseStatement(forStatement.getBody(), flow);
        ArrayList<FunApp> continues = new ArrayList<>(flow.continueFlow.getLast());
        ArrayList<FunApp> breaks = new ArrayList<>(flow.breakFlow.getLast());
        if (flow.normalFlow.isPresent()) {
            continues.add(mkFunApp(flow.normalFlow.get()));
        }
        scope.pop();
        var iterFlow = mkFunctionSymbol("for_iter", forStatement.getFileLocation());
        var iter = mkFunApp(iterFlow);
        addClauses(continues, iter);
        flow.setFlow(iterFlow);
        parseExpression(forStatement.getIterationExpression(), flow);
        var afterIterFlow = flow.normalFlow.get();
        var afterIter = mkFunApp(afterIterFlow);
        chcs.addClause(afterIter, Expression.True, pre);
        scope.pop();
        var exit = mkFunApp("for_exit", forStatement.getFileLocation());
        addClauses(breaks, exit);
        update(flow, pre, negate(cond), exit);
        flow.exitLoop();
    }

    void pop(IASTFileLocation endOfScope, Flow flow) {
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        if (scope.pop()) {
            var post = mkFunApp("end_of_scope", endOfScope);
            update(flow, pre, post);
        }
    }

    void parseIf(IASTIfStatement ifStatement, Flow flow) {
        var preFlow = flow.normalFlow.get();
        var pre = mkFunApp(preFlow);
        var exitFlow = mkFunctionSymbol("if_exit", ifStatement.getFileLocation());
        var exit = mkFunApp(exitFlow);
        var cond = parseExpression(ifStatement.getConditionExpression(), flow).toBool();
        var thenFlow = mkFunctionSymbol("if_then", ifStatement.getFileLocation());
        var then = mkFunApp(thenFlow);
        update(flow, pre, cond, then);
        scope.push();
        parseStatement(ifStatement.getThenClause(), flow);
        if (flow.normalFlow.isPresent()) {
            pop(ifStatement.getThenClause().getFileLocation(), flow);
            var afterThenFlow = flow.normalFlow.get();
            var afterThen = mkFunApp(afterThenFlow);
            chcs.addClause(afterThen, Expression.True, exit);
        } else {
            scope.pop();
        }
        if (ifStatement.getElseClause() != null) {
            var elseFlow = mkFunctionSymbol("if_else", ifStatement.getFileLocation());
            var elseApp = mkFunApp(elseFlow);
            update(flow, pre, negate(cond), elseApp);
            scope.push();
            parseStatement(ifStatement.getElseClause(), flow);
            if (flow.normalFlow.isPresent()) {
                pop(ifStatement.getElseClause().getFileLocation(), flow);
                var afterElseFlow = flow.normalFlow.get();
                var afterElse = mkFunApp(afterElseFlow);
                update(flow, afterElse, exit);
            } else {
                scope.pop();
            }
        } else {
            update(flow, pre, negate(cond), exit);
        }
    }

    void parseStatement(IASTStatement statement, Flow flow) {
        switch (statement) {
            case IASTBreakStatement breakStatement -> {
                flow.breakFlow.getLast().add(mkFunApp(flow.normalFlow.get()));
                flow.normalFlow = Optional.empty();
            }
            case IASTCaseStatement caseStatement -> throw new IllegalArgumentException("switch is not yet supported");
            case IASTContinueStatement continueStatement -> {
                flow.continueFlow.getLast().add(mkFunApp(flow.normalFlow.get()));
                flow.normalFlow = Optional.empty();
            }
            case IASTDeclarationStatement declarationStatement -> {
                switch (declarationStatement.getDeclaration()) {
                    case IASTSimpleDeclaration simpleDeclaration -> parseDeclaration(simpleDeclaration, flow);
                    default -> throw new IllegalArgumentException("unsupported declaration: " + declarationStatement.getRawSignature());
                }
            }
            case IASTCompoundStatement compoundStatement -> {
                for (var s : compoundStatement.getStatements()) {
                    parseStatement(s, flow);
                }
            }
            case IASTDoStatement doStatement -> parseDo(doStatement, flow);
            case IASTExpressionStatement expressionStatement -> parseExpression(expressionStatement.getExpression(), flow);
            case IASTForStatement forStatement -> parseFor(forStatement, flow);
            case IASTGotoStatement gotoStatement -> throw new IllegalArgumentException("goto is not yet supported");
            case IASTIfStatement ifStatement -> parseIf(ifStatement, flow);
            case IASTLabelStatement labelStatement -> {}
            case IASTNullStatement nullStatement -> {}
            case IASTReturnStatement returnStatement -> {
                var ret = returnStatement.getReturnValue();
                if (ret == null) {
                    flow.returnFlow.getLast().put(mkFunApp(flow.normalFlow.get()), Optional.empty());
                } else {
                    flow.returnFlow.getLast().put(mkFunApp(flow.normalFlow.get()), Optional.of(parseExpression(ret, flow)));
                }
                flow.normalFlow = Optional.empty();
            }
            case IASTSwitchStatement switchStatement -> throw new IllegalArgumentException("switch is not yet supported");
            case IASTWhileStatement whileStatement -> parseWhile(whileStatement, flow);
            default -> throw new IllegalArgumentException("unsupported statement: " + statement.getRawSignature());
        }
    }

    void parseFunction(IASTFunctionDefinition functionDefinition, Flow flow) {
        scope.push();
        switch (functionDefinition.getDeclarator()) {
            case IASTStandardFunctionDeclarator declarator -> {
                for (var param: declarator.getParameters()) {
                    var type = parseDeclSpecifier(param.getDeclSpecifier());
                    parseDeclarator(param.getDeclarator(), type, flow);
                }
            }
            default -> throw new IllegalArgumentException("unsupported function declarator " + functionDefinition.getDeclarator());
        }
        parseStatement(functionDefinition.getBody(), flow);
        scope.pop();
    }

    void addFunction(IASTFunctionDefinition def) {
        functions.put(def.getDeclarator().getName().toString(), def);
    }

    FunctionSymbol mkFunctionSymbol(String name, IASTFileLocation loc) {
        StringBuilder sb = new StringBuilder();
        sb.append(name);
        sb.append(HornClaus.delimiter);
        sb.append(loc.getStartingLineNumber());
        sb.append(HornClaus.delimiter);
        sb.append(loc.getNodeOffset());
        for (var c: scope.getContext().reversed()) {
            sb.append(HornClaus.delimiter);
            sb.append(c.getStartingLineNumber());
            sb.append(HornClaus.delimiter);
            sb.append(c.getNodeOffset());
        }
        return new FunctionSymbol(sb.toString(), scope.signature());
    }

    static void parseCommandlineOptions(String[] args) {
        for (int i = 0; i < args.length - 1; ++i) {
            switch (args[i]) {
                case "--ari" -> HornClaus.ari = true;
                case "--smt2" -> HornClaus.ari = false;
                case String s when s.startsWith("--delimiter=") -> HornClaus.delimiter = s.substring("--delimiter=".length());
                case "--invert" -> HornClaus.invert = true;
                default -> throw new IllegalArgumentException("unknown command line flag " + args[i]);
            }
        }
        HornClaus.filename = args[args.length - 1];
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2 && args.length != 3) {
            System.out.println("***** HornKlaus *****");
            System.out.println("usage: java -ea -jar HornKlaus.jar OPTIONS program.c");
            System.out.println("mandatory options:");
            System.out.println("    --[smt2|ari]        specifies the output format (SMT-LIB or ARI)");
            System.out.println("other options:");
            System.out.println("    --delimiter=$STRING specifies the delimiter that is used in identifiers (default: colon)");
            System.out.println("    --invert            causese HornKlaus to negate the conditions of all assertions (default: false)");
            System.exit(0);
        }
        parseCommandlineOptions(args);

        FileContent fileContent = FileContent.createForExternalFileLocation(filename);

        Map<String, String> definedSymbols = new HashMap<>();
        String[] includePaths = new String[0];
        IScannerInfo info = new ScannerInfo(definedSymbols, includePaths);
        IParserLogService log = new DefaultLogService();

        IncludeFileContentProvider emptyIncludes = IncludeFileContentProvider.getEmptyFilesProvider();

        int opts = 8;
        IASTTranslationUnit translationUnit = GCCLanguage.getDefault().getASTTranslationUnit(fileContent, info,
                emptyIncludes, null, opts, log);

        if (translationUnit.getIncludeDirectives().length > 0) {
            System.err.println("includes are not supported");
        }
        // the only argument of the start symbol is the auxiliary variable for return values
        var startFlow = new FunctionSymbol("start", List.of(Type.Int));
        HornClaus parser = new HornClaus(startFlow);
        var flow = new Flow(startFlow);
        for (var declaration : translationUnit.getDeclarations()) {
            switch (declaration) {
                case IASTSimpleDeclaration simpleDeclaration -> {
                    // TODO What's the proper way to distinguish typedefs and other declarations?
                    if (simpleDeclaration.getRawSignature().startsWith("typedef")) {
                        parser.parseTypedef(simpleDeclaration);
                    } else {
                        parser.parseDeclaration(simpleDeclaration, flow);
                    }
                }
                case IASTFunctionDefinition functionDefinition -> {
                    if (functionDefinition.getDeclarator().getName().toString().equals("main")) {
                        parser.parseFunction(functionDefinition, flow);
                    } else {
                        parser.addFunction(functionDefinition);
                    }
                }
                default -> throw new IllegalArgumentException("unsupported declaration: " + declaration);
            }
        }
        if (ari) {
            System.out.println(parser.chcs.toAri());
        } else {
            System.out.println(parser.chcs.toSexp());
        }
    }

}
