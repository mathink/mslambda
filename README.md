Map, Skeleton, Lambda.
==

Reference: [Viewing λ-terms through Maps](http://homepages.inf.ed.ac.uk/rpollack/export/Maps_SatoPollackSchwichtenbergSakurai.pdf)

Dependent on [SSReflect](http://ssr.msr-inria.inria.fr/)

Files
--

* [lambda.v](lambda.v)

  This file includes types and properties to define type ${\mathbb L}$ of lambda term.  
  I use reflection for definitions of ${\mathbb L}$.  
  Because Coq doesn't support induction-recursion, ${\mathbb L}$ is defined as sub-type of type ${\mathbb S}$ of sexp.  
  This method is described in above paper. 


TODO next
--

* implement Hole-Filling function 

  I'll use Monad as Computational-Context.

More..
--

ふと，Coq 上で λ 計算を弄りたくなった．
でも，名前の扱いが面倒だというのを過去に散々見聞きしていたので，de Bruijn も locally named も locally nameless も，まぁ，名前と雰囲気しか知らないものばかりだけど，とにかく，やる気が出なかった．
既に前例あるしね．

そんな時にふと思い出したのが上記の論文．
TPP2012 で話を聞いたなぁ，と．

そしてどうやらあまり前例もないようだし，ちょっとやってみっか，と思ってやってみている．

Coq によるエンジニアリングの練習をしたいという気持ちもあるので， Map-Skeleton の手法のみならず，色々な部分にこだわっていく予定．

ドキュメントも適度に充実させたい，が，どうなるか．
