#lang forge/temporal
open "hearthstone.frg"



/*------------------------------------*\
|    Model Properties + Verification   |
\*------------------------------------*/


/* Section 1 : test the properties of the overall model */

    -- ONLY 2 PLAYER DURING THE GAME 
pred only_two_player_join_the_game{
    always{
        all p : Player |{
           ( p = Red) or (p = Blue)
        }
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
    always {
        all t : GameTime |{
            (t.turn != t'.turn)implies{
                p.hero = Nightmare
                Nightmare.hHealth > 0
            }
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
        always{((m = S1) or (m = S2) or (m = S3) or 
        (m = S4) or (m = S5) or (m = S6) or 
        (m = S7) or (m = S8))}
    }
}



/*-------------------------------------------------*\
|   Game Procedure Properties + Verification   |
\*-------------------------------------------------*/
    --ALL PLAYER WELL-FORMED 
pred test_PlayerInitialState[p : Player] {
    /*
        Test the init state of the game
        1. All Hero intial status are set correctly
        2. All Player intial status are set correctly
        3. All Minions intial status are set correctly
    */
    (p.hero = Nightmare)
    (p.pState = PlayerLive )
    (#{p.minions} = 5)
    (noSharedMinions)
    (all_hero_init_health_greater_than_zero[p])
    (all_minion_sat_init_setup[p]) 
}

    -- NO CHANGE ON MINIONS HEALTH POINTS IF THE CURRENT IS IT'S LORD PLAYER
pred health_NoChange_check [p : Player]{
    -- Testing Guarantees No change in minion health when the current turn is its master's attack
    always (
        all t : GameTime | {
            (t.turn = p) implies {
                all m :Minion {
                    (m in p.minions) implies {t.tmHealth[m] = t'.tmHealth[m]}
                }
            }
            
        }
    )
}

    -- ALL MINION'S HEALTH POINTS = MINION.CURRENT-HEALTH - ATTCK POINTS FROM OTHER MINIONS
pred health_decresing_check[p : Player]{
    -- Testing Guarantees the m.health drop is calculated correctly when the minion is attacked.
    always (
        all t : GameTime | {
            (t.turn = p) implies {
                some m_vic : Minion |{
                    (m_vic not in p.minions) => {
                        some m_atk : Minion |{
                            (m_atk in p.minions) and 
                            t.tmHealth[m_vic] = t'.tmHealth[m_vic] + m_atk.mAttack
                        }
                    }
                }
            }
        }
    )
}

    -- MINION ->DEAD STATS IF HEALTH POINTS DROP TO 0
pred minion_state_check_A{
    -- Testing Guarantees Minion's state switch correctly 
    always(
        all t: GameTime | {
            all m : Minion | {
                (m.mHealth > 0) implies {t.tmState[m] = MinionLive}
                (m.mHealth <= 0) implies {t.tmState[m] = MinionDead}
            }
        }
    )
}

    -- MINION'S STATE SWTICH CHECK 
pred minion_state_check_B{
    -- Testing Guarantees that at minions health == 0, the minion dies and state switch correctly.
    always(
        eventually(
            all t : GameTime | {
                all m : Minion| {
                    ((t.tmHealth[m] > 0 ) and (t'.tmHealth[m] <= 0)) implies {
                        (t.tmState[m] = MinionLive) and (t'.tmState[m] = MinionDead)
                    }
                }
            }
        )
    )
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

    --LIVENESS TEST, THE GAME WILL BE END FINALLY.
pred has_winner_eventually[p:Player] {
    -- Testing Guarantees that the all games will end eventually with a winner
    always (
        eventually(
                all m : Minion |{
                    (m in p.minions)
                    (m.mHealth = 0)
                    (p.pState = PlayerDead)
                    (some winner : Player |{
                        (winner != p)
                        (winner.pState = PlayerLive)
                        (some m_winer : Minion|{
                            (m_winer in winner.minions)
                            (m_winer.mHealth != 0)
                        })
                    })
                }

        )
    )
}

    --STARVATION FREE TEST, ALL MINIONS/PLAYERS PROGRESS AT LEASTE ONCE
pred correct_turn_switch{
    always (all t : GameTime | {
        t.turn != t'.turn
    })
}
pred always_some_minion_take_action [p :Player] {
    -- Testing Guarantees that always at least one minion take action at each game state t -> t'
    always (
        all t : GameTime | {
            (t.turn = p) implies {
                some m : Minion | {
                    (m in p.minions) implies {
                        t.tmState[m] != t'.tmState[m]
                    }
                }
            }
            
        }
    )
}

pred equal_number_of_minions{
    #{Red.minions} = #{Blue.minions} 
}




test suite for traces {

    test expect {
        -- BASIC PROPERTY TESTS
        PROPERTY_BASED_TEST1 : {traces implies only_two_player_join_the_game} is sat
        PROPERTY_BASED_TEST2 : {traces implies all_hero_init_health_greater_than_zero[Player]}for exactly 2 Player is sat
        PROPERTY_BASED_TEST3 : {traces implies always_keep_validHero[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST4 : {traces implies all_minion_sat_init_setup[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST5 : {traces implies noSharedMinions[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST6 : {traces implies noUnexpectMinions} is sat


		-- OPERATIONAL TEST
        --OPERATIONAL_TEST1 : {traces implies test_PlayerInitialState[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST2 : {traces implies health_NoChange_check[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST3 : {traces implies health_decresing_check[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST4 : {traces implies minion_state_check_A} is sat
        OPERATIONAL_TEST5 : {traces implies minion_state_check_B} is theorem
        OPERATIONAL_TEST6 : {traces and some_player_has_no_minions [Player]}for exactly 2 Player is unsat
        OPERATIONAL_TEST7 : {traces and invalid_player_state_switch[Player]}for exactly 2 Player is unsat

        -- LIVENESS TEST
        LIVENESS_TEST_A : {traces implies has_winner_eventually[Player]} for exactly 2 Player is sat
        -- STARVATION FREE TEST
        STARVATION_FREE_TEST_A : {traces implies correct_turn_switch} is sat
        STARVATION_FREE_TEST_B : {traces implies always_some_minion_take_action[Player]} for exactly 2 Player is sat

    }
}












