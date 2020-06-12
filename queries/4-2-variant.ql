/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

class StepThroughMemberMethodAccess extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(MethodAccess ma |
      pred.asExpr() = ma.getQualifier() and
      succ.asExpr() = ma 
    //  flowPreservingCallable(ma.getMethod())
    )
  }
}

class StepThroughConstructor extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(ConstructorCall cc |
      pred.asExpr() = cc.getAnArgument() and
      succ.asExpr() = cc
     // flowPreservingCallable(cc.getConstructor())
    )
  }
}

class MyTaintTrackingConfig extends TaintTracking::Configuration {
  MyTaintTrackingConfig() { this = "MyTaintTrackingConfig" }

  override predicate isSource(DataFlow::Node source) {
    exists(Method m |
      m.getASourceOverriddenMethod().getQualifiedName().matches("ConstraintValidator.isValid") and
      source.asParameter() = m.getParameter(0)
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