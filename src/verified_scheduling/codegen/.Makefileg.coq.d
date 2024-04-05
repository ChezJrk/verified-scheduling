IdentParsing.vo IdentParsing.glob IdentParsing.v.beautified IdentParsing.required_vo: IdentParsing.v 
IdentParsing.vio: IdentParsing.v 
IdentParsing.vos IdentParsing.vok IdentParsing.required_vos: IdentParsing.v 
Normalize.vo Normalize.glob Normalize.v.beautified Normalize.required_vo: Normalize.v ../atl/ATL.vo ../atl/Tactics.vo ../atl/Common.vo ../atl/CommonTactics.vo ../atl/Div.vo ../atl/GenPushout.vo ../atl/Reshape.vo ../atl/LetLifting.vo IdentParsing.vo
Normalize.vio: Normalize.v ../atl/ATL.vio ../atl/Tactics.vio ../atl/Common.vio ../atl/CommonTactics.vio ../atl/Div.vio ../atl/GenPushout.vio ../atl/Reshape.vio ../atl/LetLifting.vio IdentParsing.vio
Normalize.vos Normalize.vok Normalize.required_vos: Normalize.v ../atl/ATL.vos ../atl/Tactics.vos ../atl/Common.vos ../atl/CommonTactics.vos ../atl/Div.vos ../atl/GenPushout.vos ../atl/Reshape.vos ../atl/LetLifting.vos IdentParsing.vos
CheckSafe.vo CheckSafe.glob CheckSafe.v.beautified CheckSafe.required_vo: CheckSafe.v ../atl/ATL.vo ../atl/Tactics.vo ../atl/Div.vo ../atl/Common.vo ../atl/CommonTactics.vo ../../examples/Blur.vo
CheckSafe.vio: CheckSafe.v ../atl/ATL.vio ../atl/Tactics.vio ../atl/Div.vio ../atl/Common.vio ../atl/CommonTactics.vio ../../examples/Blur.vio
CheckSafe.vos CheckSafe.vok CheckSafe.required_vos: CheckSafe.v ../atl/ATL.vos ../atl/Tactics.vos ../atl/Div.vos ../atl/Common.vos ../atl/CommonTactics.vos ../../examples/Blur.vos
NatToString.vo NatToString.glob NatToString.v.beautified NatToString.required_vo: NatToString.v 
NatToString.vio: NatToString.v 
NatToString.vos NatToString.vok NatToString.required_vos: NatToString.v 
IntToString.vo IntToString.glob IntToString.v.beautified IntToString.required_vo: IntToString.v 
IntToString.vio: IntToString.v 
IntToString.vos IntToString.vok IntToString.required_vos: IntToString.v 
CodeGen.vo CodeGen.glob CodeGen.v.beautified CodeGen.required_vo: CodeGen.v ../atl/ATL.vo ../atl/Common.vo ../atl/CommonTactics.vo ../atl/Div.vo IdentParsing.vo NatToString.vo IntToString.vo Normalize.vo
CodeGen.vio: CodeGen.v ../atl/ATL.vio ../atl/Common.vio ../atl/CommonTactics.vio ../atl/Div.vio IdentParsing.vio NatToString.vio IntToString.vio Normalize.vio
CodeGen.vos CodeGen.vok CodeGen.required_vos: CodeGen.v ../atl/ATL.vos ../atl/Common.vos ../atl/CommonTactics.vos ../atl/Div.vos IdentParsing.vos NatToString.vos IntToString.vos Normalize.vos
