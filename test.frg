#lang forge
open "hearthstone.frg"



/*------------------------------------*\
|    Model Properties + Verification   |
\*------------------------------------*/


/* Section 1 : test the properties of the overall model */

    -- ONLY 2 PLAYER DURING THE GAME 
pred only_two_player_join_the_game{
    all p : Player |{
        ( p = Red) or (p = Blue)
    }
}

    -- BUFF HERO'S HEALTH POINTS ALWAYS > 0
pred all_hero_init_health_greater_than_zero [p : Player]{
    all h: Hero | {
        (p.hero = h ) => {h.hHealth > 0}
    }
}

    -- ONLY ONE BUFF HERO CAN BE CHOSEN AND CAN NOT BE CHANGED AT ANY TIME STAMP
pred always_keep_validHero[p :Player] {
    all t1, t2 : GameTime |{
        (t1.turn != t2.turn)implies{
            p.hero = Nightmare
            Nightmare.hHealth > 0
        }
    }
}

    -- ALL MINIONS LIMITED BY DEFAULT CONSTAINS
pred all_minion_sat_init_setup[p : Player]{
    /* Ensures all Minion's State within boundaries */
    all m : Minion | {
       ( m in p.minions) implies {
            m.mAttack >= 0
            m.mHealth > 0
            m.mAction = NotAction
            m.mState = MinionLive
       }
    }
}
    -- NO MINION CAN BE SHAPED BY DIFFERENT PLAYER
pred noSharedMinions[p : Player]{
    /* Ensures non-shared minions of different player */
    #{Red.minions & Blue.minions} = 0
}

    -- NO "UN-EXPECTED EXTRA MINON(S)" DURING THE GAME 
pred noUnexpectMinions {
    -- Testing Guarantees that all minions in minions set
    all m : Minion {
        ((m = S1) or (m = S2) or (m = S3) or 
        (m = S4))
    }
}

/* New test adding */

    -- No Game State.next points to First state, Acyclic TEST
pred noFirstStatePrev{
    all t : GameTime |{
        Game.next[t] != firstState
    }
}

    -- Final state.next should always points to some NONE STATES
pred noEndingStateNext{
    some t : GameTime |{
        Game.next[t] = none
    }
}
    -- No Game STATE prev than First state are Reachable
pred noFirstStatePrevReachable{
    all t1, t2 : GameTime |{
        ((t1 != t2) and (Game.next[t1] = t2)) => {(Game.next[t2] != firstState)}
    }
}
    -- No Circle
pred noCircleTest[t : GameTime]{
        all t1, t2 : GameTime |{
        ((t1 != t2) and (Game.next[t1] = t2)) implies {Game.next[t2] != t1}
    }
}



/*-------------------------------------------------*\
|   Game Procedure Properties + Verification   |
\*-------------------------------------------------*/
    --ALL PLAYER WELL-FORMED 
// pred test_PlayerInitialState[p : Player]{
//     /*
//         Test the init state of the game
//         1. All Hero intial status are set correctly
//         2. All Player intial status are set correctly
//         3. All Minions intial status are set correctly
//     */
//     (p.hero = Nightmare)
//     (p.pState = PlayerLive )
//     (#{p.minions} = 5)
//     (noSharedMinions)
//     (all_hero_init_health_greater_than_zero[p])
//     (all_minion_sat_init_setup[p]) 
// }

    -- NO CHANGE ON MINIONS HEALTH POINTS IF THE CURRENT IS IT'S LORD PLAYER
pred health_NoChange_check [p : Player]{
    -- Testing Guarantees No change in minion health when the current turn is its master's attack
    all t1, t2 : GameTime | {
        (t1 != t2)
        (t1.turn = p) implies {
            all m :Minion {
                (m in p.minions) implies {t1.tmHealth[m] = t2.tmHealth[m]}
            }
        }
    }
}

    -- ALL MINION'S HEALTH POINTS = MINION.CURRENT-HEALTH - ATTCK POINTS FROM OTHER MINIONS
pred health_decresing_check[p : Player]{
    -- Testing Guarantees the m.health drop is calculated correctly when the minion is attacked.
    all t1, t2 : GameTime | {
        (t1 != t2)
        (t1.turn = p) implies {
            some m_vic : Minion |{
                (m_vic not in p.minions) => {
                    some m_atk : Minion |{
                        (m_atk in p.minions) and 
                        t1.tmHealth[m_vic] = t2.tmHealth[m_vic] + m_atk.mAttack
                    }
                }
            }
        }
    }
}

    -- MINION ->DEAD STATS IF HEALTH POINTS DROP TO 0
pred minion_state_check_A{
    -- Testing Guarantees Minion's state switch correctly 
    all t: GameTime | {
        all m : Minion | {
            (m.mHealth > 0) implies {t.tmState[m] = MinionLive}
            (m.mHealth <= 0) implies {t.tmState[m] = MinionDead}
        }
    }
}

    -- MINION'S STATE SWTICH CHECK 
pred minion_state_check_B{
    -- Testing Guarantees that at minions health == 0, the minion dies and state switch correctly.
    all t1, t2 : GameTime | {
        (t1 != t2)
        all m : Minion| {
            ((t1.tmHealth[m] > 0 ) and (t2.tmHealth[m] <= 0)) implies {
                (t1.tmState[m] = MinionLive) and (t2.tmState[m] = MinionDead)
            }
        }
    }
}

pred some_player_has_no_minions [p : Player]{
    -- Testing Guarantees that the player's minions set can not be empty
    some p : Player | {
        #{p.minions} = 0
    }
}

pred invalid_player_state_switch[p:Player]{
    -- Testing Guarantees that player's state only switch to dead iff all minion's health = 0
    some m : Minion |{
        (m in p.minions)
        (m.mHealth != 0)
        (p.pState = PlayerDead)
    }
}


--------------- Done ----------------

    --LIVENESS TEST, THE GAME WILL BE END FINALLY.
pred has_winner_eventually{
    -- Testing Guarantees that the all games will end eventually with a winner
        -- 1. There is a final state, such taht s.next = none
        -- 2. For the last state: 
            -- at least one winner's minion state = alive , and health points <= 0
            -- all loser's minion state = Dead, and health points > 0
    one last : GameTime | {
        (no Game.next[last])
        (some p1, p2 :Player |{
            (p1 != p2)
            (all m1 : Minion|{
                (m1 in p1.minions)
                (last.tmHealth[m1] <= 0)
                (m1.mState = MinionDead)
            })
            (some m2 : Minion|{
                (m2 in p2.minions)
                (m2.mState = MinionLive)
                (last.tmHealth[m2] > 0)
            })
        })
    }
}

pred get_adjacent_gametime[t1, t2 :GameTime]{
    -- Generate a t1->t2 pair, which is t1 is head and t2 is tail
        -- t1 and t2 both are not last GameTime
    one last : GameTime |{
        (no Game.next[last])
        (t1 != last)
        (t2 != last)
        (t1 !=  t2)
        (Game.next[t1] = t2)
    }
}
    --STARVATION FREE TEST, ALL MINIONS/PLAYERS PROGRESS AT LEASTE ONCE
pred correct_turn_switch{
    all t1, t2 :GameTime |{
        get_adjacent_gametime[t1, t2]
        t1.turn != t2.turn
    }
}
pred always_some_minion_take_action{
    -- Testing Guarantees that always at least one minion take action at each game state t -> t'
    all t1, t2 : GameTime |{
        get_adjacent_gametime[t1, t2]
        all m : Minion |{
            (m in t1.turn.minions)
            (t1.tmState[m] != t2.tmState[m])
        }
    }
}

test suite for traces {

    test expect {
        -- BASIC PROPERTY TESTS
        // PROPERTY_BASED_TEST1 : {traces implies only_two_player_join_the_game} is sat
        // PROPERTY_BASED_TEST2 : {traces implies all_hero_init_health_greater_than_zero[Player]}for exactly 2 Player is sat
        // PROPERTY_BASED_TEST3 : {traces implies always_keep_validHero[Player]} for exactly 2 Player is sat
        // PROPERTY_BASED_TEST4 : {traces implies all_minion_sat_init_setup[Player]} for exactly 2 Player is sat
        // PROPERTY_BASED_TEST5 : {traces implies noSharedMinions[Player]} for exactly 2 Player is sat
        // PROPERTY_BASED_TEST6 : {traces implies noUnexpectMinions} is sat


		// // -- OPERATIONAL TEST
        // --OPERATIONAL_TEST1 : {traces implies test_PlayerInitialState[Player]}for exactly 2 Player is sat
        // OPERATIONAL_TEST2 : {traces implies health_NoChange_check[Player]}for exactly 2 Player is sat
        // OPERATIONAL_TEST3 : {traces implies health_decresing_check[Player]}for exactly 2 Player is sat
        // OPERATIONAL_TEST4 : {traces implies minion_state_check_A} is sat
        // OPERATIONAL_TEST5 : {traces implies minion_state_check_B} is sat
        // OPERATIONAL_TEST6 : {traces and some_player_has_no_minions [Player]}for exactly 2 Player is unsat
        // OPERATIONAL_TEST7 : {traces and invalid_player_state_switch[Player]}for exactly 2 Player is unsat

        -- LIVENESS TEST
        LIVENESS_TEST_A : {traces implies has_winner_eventually} is sat
        -- STARVATION FREE TEST
        STARVATION_FREE_TEST_A : {traces implies correct_turn_switch} is sat
        STARVATION_FREE_TEST_B : {traces implies always_some_minion_take_action} is sat 

    }
}












