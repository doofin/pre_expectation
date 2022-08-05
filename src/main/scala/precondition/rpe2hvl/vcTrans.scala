package precondition.rpe2hvl

object vcTrans {
  type Stmts = Seq[String]
  type Expr = String
  type Expectation = String // expectation number
  // proving upper bound, vc[𝑆](𝜌) ⊑ 𝜑 ,p46
  //𝜌:post, 𝜑:bound
  def upperB(S: Stmts, post: Expectation, bound: Expectation): Stmts = {
    s"down negate; up assume 𝜑; 𝑆; up assert 𝜌; up negate".split(";").toSeq
  }

  def ifTrans(e1: Expr, e2: Expr, s1: Stmts, s2: Stmts): Stmts = {
    s"""if (⊓) {
            down assume ?($e1=$e2); 
          if (⊓) { 
            down assume ?($e1 && $e2); 
            $s1 
            } 
          else { 
          down assume ?($e1 & $e2); 
          $s2 
          } 
        } 
        else {
        down assume ?(($e1=$e2)); 
        down assume 0 
        } """
    Seq()
  }

  def whileTrans(e1: Expr, e2: Expr, s: Stmts, invar: Expectation): Stmts = {
    s"""
    down assert $invar;
    down negate;
    up compare $invar
    if (⊓) {
            down assume ?($e1=$e2); 
            if (⊓) { 
            down assume ?($e1 && $e2);
            $s ;
            down assert $invar;
            down assume 0;
            } 
            else { 
            down assume ?($e1 & $e2);
            } 
             } 
    else {
        down assume ?(($e1=$e2)); 
        down assume 0 ;
        } """
    Seq()
  }
  def test = {
    val (e1w, e2w) = ("", "")
    val (e1if, e2if) = ("", "")
    val (post, bound) = ("", "")
    // upperB(whileTrans(e1w, e2w, ifTrans(e1if, e2if, Seq(), Seq())), post, bound)
  }
}

// Expected one of "!=", "&&", "(", ")", "*", "+", ",", "-", ";", "<", "<=", "==", ">", ">=", "]",
//"axiom", "domain", "down", "ensures", "func", "proc", "requires", "up", "{", "||", "}",
// "←", "→", "↖", "↘", "⊓", or "⊔"
