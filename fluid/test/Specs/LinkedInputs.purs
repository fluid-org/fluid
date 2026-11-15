module Test.Specs.LinkedInputs where

import App.Util (Selector)
import App.Util.Selector (eachElement, envVal, field, valOf, listElement, select, none, (>.>))
import Bind ((↦))
import Data.Maybe (Maybe(..))
import Test.Util (fluidSrcPaths)
import Test.Util.Suite (TestLinkedInputsSpec)
import Val (Val)

yearAndCountry :: Selector Val
yearAndCountry = eachElement (field "year" select >.> field "country" select)

linkedInputs_spec3 :: TestLinkedInputsSpec
linkedInputs_spec3 =
   { spec:
        { fluidSrcPaths
        , ignoreInputs: envVal "renewables" (valOf yearAndCountry) >.> envVal "nonRenewables" (valOf yearAndCountry)
        , linking: true
        , rowFilter: Nothing
        }
   , δ_in: "nonRenewables" ↦ listElement 51 (field "coalCap" select)
   , in_expect:
        envVal "nonRenewables"
           ( valOf
                ( listElement 51
                     ( field "coalCap" select
                          >.> field "gasCap" select
                          >.> field "nuclearCap" select
                          >.> field "petrolCap" select
                     )
                )
           ) >.>
           envVal "renewables"
              ( valOf
                   ( listElement 204 (field "capacity" select)
                        >.> listElement 205 (field "capacity" select)
                        >.> listElement 206 (field "capacity" select)
                        >.> listElement 207 (field "capacity" select)
                   )
              )
   , file: "linked_inputs/energyscatter.fld"
   }

linkedInputs_spec4 :: TestLinkedInputsSpec
linkedInputs_spec4 =
   { spec:
        { fluidSrcPaths
        , ignoreInputs: envVal "renewables" (valOf yearAndCountry) >.> envVal "nonRenewables" (valOf yearAndCountry)
        , linking: true
        , rowFilter: Nothing
        }
   , δ_in: "renewables" ↦ listElement 204 (field "capacity" select)
   , in_expect:
        envVal "nonRenewables"
           ( valOf
                ( listElement 51
                     ( field "coalCap" select
                          >.> field "gasCap" select
                          >.> field "nuclearCap" select
                          >.> field "petrolCap" select
                          >.> field "nuclearOut" select
                     )
                )
           )
           >.> envVal "renewables"
              ( valOf
                   ( listElement 204 (field "capacity" select >.> field "output" select)
                        >.> listElement 205 (field "capacity" select >.> field "output" select)
                        >.> listElement 206 (field "capacity" select >.> field "output" select)
                        >.> listElement 207 (field "capacity" select >.> field "output" select)
                   )
              )
   , file: "linked_inputs/energyscatter.fld"
   }

linkedInputs_spec5 :: TestLinkedInputsSpec
linkedInputs_spec5 =
   { spec:
        { fluidSrcPaths
        , ignoreInputs: none
        , linking: true
        , rowFilter: Nothing
        }
   , δ_in: "nonRenewables" ↦ listElement 0 (field "coalCap" select)
   , in_expect:
        envVal "nonRenewables"
           ( valOf
                ( listElement 0
                     ( field "coalCap" select
                          >.> field "gasCap" select
                          >.> field "nuclearCap" select
                          >.> field "petrolCap" select
                     )
                )
           )
           >.> envVal "renewables"
              ( valOf
                   ( listElement 0 (field "capacity" select)
                        >.> listElement 1 (field "capacity" select)
                        >.> listElement 2 (field "capacity" select)
                        >.> listElement 3 (field "capacity" select)
                   )
              )
   , file: "linked_inputs/mini_energyscatter.fld"
   }

linkedInputs_cases :: Array TestLinkedInputsSpec
linkedInputs_cases =
   [ linkedInputs_spec3
   , linkedInputs_spec4
   , linkedInputs_spec5
   ]
