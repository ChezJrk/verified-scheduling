ATL.vo ATL.glob ATL.v.beautified ATL.required_vo: ATL.v 
ATL.vio: ATL.v 
ATL.vos ATL.vok ATL.required_vos: ATL.v 
Tactics.vo Tactics.glob Tactics.v.beautified Tactics.required_vo: Tactics.v ATL.vo
Tactics.vio: Tactics.v ATL.vio
Tactics.vos Tactics.vok Tactics.required_vos: Tactics.v ATL.vos
Relations.vo Relations.glob Relations.v.beautified Relations.required_vo: Relations.v 
Relations.vio: Relations.v 
Relations.vos Relations.vok Relations.required_vos: Relations.v 
Invariant.vo Invariant.glob Invariant.v.beautified Invariant.required_vo: Invariant.v Relations.vo
Invariant.vio: Invariant.v Relations.vio
Invariant.vos Invariant.vok Invariant.required_vos: Invariant.v Relations.vos
Sets.vo Sets.glob Sets.v.beautified Sets.required_vo: Sets.v 
Sets.vio: Sets.v 
Sets.vos Sets.vok Sets.required_vos: Sets.v 
ModelCheck.vo ModelCheck.glob ModelCheck.v.beautified ModelCheck.required_vo: ModelCheck.v Invariant.vo Relations.vo Sets.vo
ModelCheck.vio: ModelCheck.v Invariant.vio Relations.vio Sets.vio
ModelCheck.vos ModelCheck.vok ModelCheck.required_vos: ModelCheck.v Invariant.vos Relations.vos Sets.vos
Var.vo Var.glob Var.v.beautified Var.required_vo: Var.v 
Var.vio: Var.v 
Var.vos Var.vok Var.required_vos: Var.v 
Map.vo Map.glob Map.v.beautified Map.required_vo: Map.v Sets.vo
Map.vio: Map.v Sets.vio
Map.vos Map.vok Map.required_vos: Map.v Sets.vos
FrapWithoutSets.vo FrapWithoutSets.glob FrapWithoutSets.v.beautified FrapWithoutSets.required_vo: FrapWithoutSets.v Sets.vo Map.vo Var.vo Invariant.vo ModelCheck.vo Relations.vo
FrapWithoutSets.vio: FrapWithoutSets.v Sets.vio Map.vio Var.vio Invariant.vio ModelCheck.vio Relations.vio
FrapWithoutSets.vos FrapWithoutSets.vok FrapWithoutSets.required_vos: FrapWithoutSets.v Sets.vos Map.vos Var.vos Invariant.vos ModelCheck.vos Relations.vos
Div.vo Div.glob Div.v.beautified Div.required_vo: Div.v Tactics.vo FrapWithoutSets.vo
Div.vio: Div.v Tactics.vio FrapWithoutSets.vio
Div.vos Div.vok Div.required_vos: Div.v Tactics.vos FrapWithoutSets.vos
Common.vo Common.glob Common.v.beautified Common.required_vo: Common.v ATL.vo Tactics.vo Div.vo
Common.vio: Common.v ATL.vio Tactics.vio Div.vio
Common.vos Common.vok Common.required_vos: Common.v ATL.vos Tactics.vos Div.vos
CommonTactics.vo CommonTactics.glob CommonTactics.v.beautified CommonTactics.required_vo: CommonTactics.v ATL.vo Tactics.vo Div.vo Common.vo
CommonTactics.vio: CommonTactics.v ATL.vio Tactics.vio Div.vio Common.vio
CommonTactics.vos CommonTactics.vok CommonTactics.required_vos: CommonTactics.v ATL.vos Tactics.vos Div.vos Common.vos
LetLifting.vo LetLifting.glob LetLifting.v.beautified LetLifting.required_vo: LetLifting.v ATL.vo Common.vo Tactics.vo CommonTactics.vo
LetLifting.vio: LetLifting.v ATL.vio Common.vio Tactics.vio CommonTactics.vio
LetLifting.vos LetLifting.vok LetLifting.required_vos: LetLifting.v ATL.vos Common.vos Tactics.vos CommonTactics.vos
GenPushout.vo GenPushout.glob GenPushout.v.beautified GenPushout.required_vo: GenPushout.v ATL.vo Common.vo Tactics.vo Div.vo CommonTactics.vo
GenPushout.vio: GenPushout.v ATL.vio Common.vio Tactics.vio Div.vio CommonTactics.vio
GenPushout.vos GenPushout.vok GenPushout.required_vos: GenPushout.v ATL.vos Common.vos Tactics.vos Div.vos CommonTactics.vos
Reshape.vo Reshape.glob Reshape.v.beautified Reshape.required_vo: Reshape.v ATL.vo Tactics.vo Common.vo CommonTactics.vo Div.vo GenPushout.vo LetLifting.vo
Reshape.vio: Reshape.v ATL.vio Tactics.vio Common.vio CommonTactics.vio Div.vio GenPushout.vio LetLifting.vio
Reshape.vos Reshape.vok Reshape.required_vos: Reshape.v ATL.vos Tactics.vos Common.vos CommonTactics.vos Div.vos GenPushout.vos LetLifting.vos
PairElimination.vo PairElimination.glob PairElimination.v.beautified PairElimination.required_vo: PairElimination.v ATL.vo Common.vo CommonTactics.vo Tactics.vo Div.vo
PairElimination.vio: PairElimination.v ATL.vio Common.vio CommonTactics.vio Tactics.vio Div.vio
PairElimination.vos PairElimination.vok PairElimination.required_vos: PairElimination.v ATL.vos Common.vos CommonTactics.vos Tactics.vos Div.vos
