/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph
import semmle.code.java.dataflow.FlowSources


predicate flowPreservingCallable(Callable m) {
  exists(string s |
    s = m.getName() and
    (
      s = "getSoftConstraints" or
      s = "getHardConstraints" or
      s = "keySet" or
      s = "stream" or
      s = "map" or
      s = "collect" or
      s.matches("HashSet%")
    )
  )
}

class StepThroughMemberMethodAccess extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(MethodAccess ma |
      pred.asExpr() = ma.getQualifier() and
      succ.asExpr() = ma and
      flowPreservingCallable(ma.getMethod())
    )
  }
}

class StepThroughConstructor extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(ConstructorCall cc |
      pred.asExpr() = cc.getAnArgument() and
      succ.asExpr() = cc and
      flowPreservingCallable(cc.getConstructor())
    )
  }
}

class StepThroughConstraintAnnotation extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Constructor c, Field f |
      pred.asParameter() = c.getAParameter() and
      f.getName() = pred.asParameter().getName() and
      succ.asParameter() = annotedWithValidator(f).getAParameter()
    )
  }
}

class StepThroughGRPCClasses extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(RefType rt |
      pred instanceof RemoteFlowSource and
      pred.getType().(RefType).getPackage().getName().matches("%.grpc.protogen") and
      rt.getName() = pred.getType().getName() and
      rt.getAConstructor().getAParameter() = succ.asParameter()
    )
  }
}

Field getAFieldRecursively(Type t) {
  exists(Field f |
    result = f or
    result = getAFieldRecursively(f.getType())
  )
}

Method annotedWithValidator(Field f) {
  exists(Annotation a, Method m |
    (a.getAnnotatedElement() = f.getType() or a.getAnnotatedElement() = f) and
    m.getASourceOverriddenMethod().getQualifiedName().matches("ConstraintValidator.isValid") and
    a.getType().getEnclosingType().getAMethod() = m and
    result = m
  )
}

Annotation validatingAnnotation() {
  exists(Annotation a |
    a
        .getType()
        .getEnclosingType()
        .getAMethod()
        .getASourceOverriddenMethod()
        .getQualifiedName()
        .matches("ConstraintValidator.isValid") and
    result = a
  )
}


class MyTaintTrackingConfig extends TaintTracking::Configuration {
  MyTaintTrackingConfig() { this = "MyTaintTrackingConfig" }

  override predicate isSource(DataFlow::Node source) {
    exists(DataFlow::Node apiEndpoint, RefType t, Field f, Constructor c |
      apiEndpoint instanceof RemoteFlowSource and
      t.getName() = apiEndpoint.getType().getName() and //gRPC class is different from class but with same name (separate packages)
      f = getAFieldRecursively(t) and
      (
        f.getAnAnnotation() = validatingAnnotation() or
        f.getType().(RefType).getAnAnnotation() = validatingAnnotation()
      ) and
      c = f.getAnAccess().getEnclosingCallable() and
      source.asParameter() = c.getAParameter() and
      source.asParameter().getName() = f.getName()
    )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(MethodAccess ma |
      ma.getMethod().getQualifiedName() =
        "ConstraintValidatorContext.buildConstraintViolationWithTemplate" and
      ma.getArgument(0) = sink.asExpr()
    )
  }
}

from MyTaintTrackingConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"