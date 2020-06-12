import java
import semmle.code.java.dataflow.DataFlow

predicate isSink(DataFlow::Node sink) {
  exists(MethodAccess ma |
    ma.getMethod().getQualifiedName() =
      "ConstraintValidatorContext.buildConstraintViolationWithTemplate" and
    ma.getArgument(0) = sink.asExpr()
  )
}

select "Quick-eval isSink"
