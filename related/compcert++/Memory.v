Require Import Coqlib.
Load Param.
Open Scope Z_scope.


  Section Mem.

  Variable val : Type.

  Record valop : Type := Valop {
    valsize : val -> Z;
    valalign : val -> Z
  }.

  Variables (memblocks : Type) (memvalues : Type) (mblock : Type).

  Record op : Type := Op {
    initmembl : memblocks;
    initmemval : memvalues;
    valid_block : memblocks -> mblock -> Prop;
    mblock_eq_dec : forall b1 b2 : mblock, {b1 = b2} + {b1 <> b2};
    alloc : memblocks -> Z -> (mblock * memblocks);
    block_size : memblocks -> mblock -> Z;
    free : memblocks -> mblock -> memblocks;
    load : Z -> memblocks -> memvalues -> mblock * Z -> option val;
    store : Z -> memblocks -> memvalues -> mblock * Z -> val -> option memvalues
  }.

  Variable o : op.
  Variable v : valop.

  Record prop : Prop := intro {

   (** The following axiom is the only needed way to store a value into memory: it requires the alignment to divide the offset, and the chunk size to be equal to the size of the actual data being written. *)
   
   store_some : forall i mv,
     (valalign v mv | i) ->
     forall memb b, 
       valid_block o memb b ->
       0 <= i -> i + valsize v mv <= block_size o memb b ->
       forall memv,
         store o (valsize v mv) memb memv (b, i) mv <> None
         ;

   load_store_same : forall i sz mv memb memv memv',
     store o sz memb memv i mv = Some memv' ->
     load o sz memb memv' i = Some mv
       ;

   load_store_other : forall memb memv b i mv sz' memv',
     store o sz' memb memv (b, i) mv = Some memv' ->
     forall b' j sz,
       b' <> b \/ (j + sz <= i \/ i + sz' <= j) ->
       load o sz memb memv' (b', j) = load o sz memb memv (b', j)
         ;

    alloc_invalid_before : forall memb b' memb' sz,
      alloc o memb sz = (b', memb') ->
      valid_block o memb b' -> False
      ;

    alloc_valid_same : forall m b' m' sz,
      alloc o m sz = (b', m') ->
      valid_block o m' b';

    alloc_valid_other : forall m b' m' sz,
      alloc o m sz = (b', m') ->
      forall b, valid_block o m b -> valid_block o m' b
        ;

    free_valid_other : forall b b',
      b' <> b ->
      forall m,
      valid_block o m b' -> valid_block o (free o m b) b'
      ;

    load_alloc : forall memb b' memb' sz,
      alloc o memb sz = (b', memb') ->
      forall sz' memv bi,
        load o sz' memb' memv bi =
          load o sz' memb memv bi
            ;

    load_free_other : forall b b',
      b' <> b ->
      forall o sz memb memv i,
        load o sz (free o memb b) memv (b', i) =
          load o sz memb memv (b', i)
            ;

    alloc_block_size_same : forall m b' m' sz,
      alloc o m sz = (b', m') ->
      block_size o m' b' = sz
      ;

    alloc_block_size_other : forall m b' m' sz,
      alloc o m sz = (b', m') ->
      forall b, b' <> b ->
        block_size o m' b = block_size o m b
        ;

    free_block_size_other : forall b b',
      b' <> b ->
      forall o memb,
        block_size o (free o memb b) b' = block_size o memb b'

}.

End Mem.
