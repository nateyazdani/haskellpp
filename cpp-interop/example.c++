class Expr {
public:
  unsigned _src_pos;
  unsigned _src_len;
};

class InfixExpr : Expr {
public:
  Expr *_lhs;
  Expr *_rhs;
};

class PlusExpr : InfixExpr { };
class MinusExpr : InfixExpr { };

class CallExpr : Expr {
public:
  Expr *_fun;
  Expr *_arg;
};

class NumeralExpr : Expr {
public:
  int _lit;
};
