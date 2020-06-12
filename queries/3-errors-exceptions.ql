import java
import semmle.code.java.dataflow.TaintTracking

predicate methodMightWriteErrorMessage(Method m) {
  m.getParameterType(_).getName() = "String" and
  not (
    m.getName().matches("%assert%") or
    m.getName().matches("%format%")
  )
}

class StepThroughExceptionThrow extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
    exists(
      TryStmt ts, FieldAccess fa, CatchClause cc, MethodAccess ma, MethodAccess ma2, Exception e
    |
      cc.getTry() = ts and
      pred.asExpr().getEnclosingStmt() = ts.getBlock().getAChild*() and
      succ.asExpr().getEnclosingStmt() = cc.getBlock().getAChild*() and
      pred.asExpr() = ma.getAnArgument() and
      ma.getMethod().getAThrownExceptionType().getASupertype*() = cc.getACaughtType() and
      succ.asExpr() = ma2 and
      (
        cc.getVariable().getAnAccess() = ma2.getAnArgument().getAChildExpr*()
        or
        cc.getVariable().getAnAccess() = fa.getQualifier() and
        ma2.getAnArgument().getAChildExpr*() = fa
      ) and
      methodMightWriteErrorMessage(ma2.getMethod())
    )
  }
}

select "Quick-eval step function"
