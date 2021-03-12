import "correspondence"

signature KNOWLEDGE =
sig
  type base

  (* CSpace knowledge *)


  (* Relational knowledge *)
  val relationsOf : base -> Relation.relationship Set.T;
  val related : base -> Relation.T -> 'a -> 'b -> bool;
  val subrelation : base -> Relation.T -> Relation.T -> bool;

  (* Correspondence knowledge *)
  val correspondencesOf : base -> Correspondence.T Set.T;

  (* Building a knowledge base *)
  val addCorrespondences : base -> Correspondence.T list -> base;
  val addRelationships : base -> Relation.relationship list -> base;

  val make : Relation.relationship list -> Correspondence.T list -> CSpace.T -> base;

end

structure Knowledge : KNOWLEDGE =
struct
  type base = {relationships : Relation.relationship Set.T,
               subrelation : Relation.T * Relation.T -> bool,
               correspondences : Correspondence.T Set.T,
               cspace : CSpace.T};

  (* CSpace knowledge *)
  (* nothing for now*)

  (* Relational knowledge *)
  fun relationshipsOf KB = #relationships KB;
  fun subrelation KB R1 R2 = (#subrelation KB) (R1,R2);

  fun related KB R a b =
  let val alwaysTrue = Relation.alwaysTrue (Relation.leftTypeOf R) (Relation.rightTypeOf R)
      fun sat (x,y,R') = SGraph.sameV x a andalso SGraph.sameV y b andalso subrelation KB R' R
  in Relation.same R alwaysTrue orelse Option.isSome (Set.find sat (relationshipsOf KB))
  end;

  (* Correspondence knowledge *)
  fun correspondencesOf KB = #correspondences KB;

  (* Building a knowledge base *)
  fun addCorrespondences KB corrs =
    {relationships= #relationships KB,
      subrelation = #subrelation KB,
      correspondences = List.foldl Set.insert (#correspondences KB) corrs,
      cspace = #cspace KB}

  fun addRelationships KB rels =
    {relationships= List.foldl Set.insert (#relationships KB) rels,
      subrelation = #subrelation KB,
      correspondences = #correspondences KB,
      cspace = #cspace KB}

  (* for now, the subrelation function is simply reflexive *)
  fun make rels corrs cs =
  let fun subrel (R1,R2) = if Relation.same (R1,R2) then true else false
  in {relationships= Set.fromList rels,
      subrelation = subrel,
      correspondences = Set.fromList corrs,
      cspace = cs}
  end

end
