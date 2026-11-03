!R = !runtime.capability<rng, "bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%choice:i1,%a:!R,%b:!R):
   %out:2 = "protocol.repeat"(%n,%a,%b,%choice) ({
   ^loop(%i:ui64,%old_a:!R,%old_b:!R,%enabled:i1):
     %selected:2 = "protocol.branch"(%enabled,%old_a,%old_b) ({
     ^then(%left:!R,%right:!R):
       "protocol.yield"(%left,%right) : (!R,!R)->()
     }, {
     ^else(%left:!R,%right:!R):
       "protocol.yield"(%left,%right) : (!R,!R)->()
     }) {site="choose",roles=["P"],output_roles=[["P"],["P"]],alternatives=["then","else"]} : (i1,!R,!R)->(!R,!R)
     "protocol.yield"(%selected#0,%selected#1) : (!R,!R)->()
   }) {site="rounds",carried=2:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!R,!R,i1)->(!R,!R)
   "protocol.return"(%out#0,%out#1) : (!R,!R)->()
 }) {sym_name="main",function_type=(ui64,i1,!R,!R)->(!R,!R),roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
