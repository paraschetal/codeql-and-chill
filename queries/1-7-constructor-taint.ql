/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PartialPathGraph // this is different!

predicate flowPreservingCallable(Callable m) {
  exists(string s |
    s = m.getName() and
    (
      s = "getSoftConstraints" or
      s = "getHardConstraints" or
      s = "keySet" or
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

  override int explorationLimit() { result = 10 } // this is different!
}

from MyTaintTrackingConfig cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
  cfg.hasPartialFlow(source, sink, _) and
  source.getNode().asParameter().getName() = "container" // DONE restrict to the one source we are interested in, for ease of debugging
select sink, source, sink, "Partial flow from unsanitized user data"

predicate partial_flow(DataFlow::PartialPathNode n, DataFlow::Node src, int dist) {
  exists(MyTaintTrackingConfig conf, DataFlow::PartialPathNode source |
    conf.hasPartialFlow(source, n, dist) and
    src = source.getNode() and
    src.asParameter().getName() = "container" // DONE - restrict to THE source we are interested in
  )
}
