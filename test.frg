#lang forge/temporal
open "hearthstone.frg"

/****************************************
* Section 1 : Init State Test           *
* Basic Property Test                   *
****************************************/


-- 1.1 Player Init state testing 
pred test_PlayerInitialState {
    /*
        Test the init state of the game
        1. All Heros are set correctly
        2. All Player are set correctly
        3. All Minions are set correctly
    */

    all p : Player | {
        (p.hero = Nightmare)
        (p.pState = PlayerLive )
        (#{p.minions} = 5)
        (noSharedMinions)
        (validHeroState[p])
        (validMinionState[p])
    }
}
pred validHeroState [p : Player]{
    /*
        Ensures all hero's init health within boundaries
    */
    all h: Hero | {
        (p.hero = h ) => {h.hHealth > 0}
    }
}
pred validMinionState[p : Player]{
    /*
        Ensures all Minion's State within boundaries
    */
    all m : Minion | {
       ( m in p.minions) implies {
            m.mAttack >= 0
            m.mHealth > 0
            m.mAction = NotAction
            m.mState = MinionLive
       }
    }
}
pred noSharedMinions{
    /*
        Ensures non-shared minions of different player
    */
    #{Red.minions & Blue.minions} = 0
}

-- Init Case testing

pred noUnexpectMinions {
    --1.2 Minions testing
    all m : Minion {
        always{((m = S1) or (m = S2) or (m = S3) or 
        (m = S4) or (m = S5) or (m = S6) or 
        (m = S7) or (m = S8) or (m = S9) or 
        (m = S10))}
    }
}
pred validHero {
     --1.3 Hero state s --> s' undead checking 
    always{all h : Hero {
        h.hHealth > 0
    }}
}

/****************************************
* Section 2 : State transfer test       * 
****************************************/

/*
 Testing 2.1 :  Liveness property testing
*/
pred has_winner_eventually {
    -- Testing Guarantees that the all games will end eventually with a winner
    always (eventually(
    (all m : Minion |{
        (m in Blue.minions) implies {(m.mState = MinionDead) and (m.mHealth = 0)}
    })
    or 
    (all m : Minion |{
        (m in Red.minions) implies {(m.mState = MinionDead) and (m.mHealth = 0)}
    })
    ))
}

pred At_least_one_player_was_terminated {
    -- Testing Guarantees that one of player will dead eventually and game end 
    always (
        eventually(
            all p : Player {
                all m : Minion |{
                    (m in p.minions) and (m.mHealth = 0)
                } implies {
                    p.pState = PlayerDead
                }
            }
        )
    )
}

/*
Testing 2.2 ： Starvation free testing
*/
pred correct_turn_switch{
    always (all t : GameTime | {
        t.turn != t'.turn
    })
}
pred always_some_minion_take_action {
    -- Testing Guarantees that always at least one minion take action at each game state t -> t'
    always (
        all t : GameTime | {
            all p : Player | {
                (t.turn = p) implies {
                    some m : Minion | {
                        (m in p.minions) implies {
                            t.tmState[m] != t'.tmState[m]
                        }
                    }
                }
            }
        }
    )
}

/*
    Testing 2.3： Game running rules and logical boundary testing
*/
pred health_NoChange_check {
    -- Testing Guarantees No change in minion health when the current turn is its master's attack
    always (
        all t : GameTime | {
            all p : Player | {
                (t.turn = p) implies {
                    all m :Minion {
                        (m in p.minions) implies {t.tmHealth[m] = t'.tmHealth[m]}
                    }
                }
            }
        }
    )
}

pred health_decresing_check{
    -- Testing Guarantees the m.health drop is calculated correctly when the minion is attacked.
    always (
        all t : GameTime | {
            all p : Player | {
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
        }
    )
}

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


pred some_player_has_no_minions {
    -- Testing Guarantees that the player's minions set can not be empty
    some p : Player | {
        #{p.minions} = 0
    }
}

pred some_invalid_player{
    -- Testing Guarantees that only 2 player join the game
    always(some p : Player | {
        (p!= Red)
        (p!= Blue)
    })
}

pred invalid_player_state_switch{
    -- Testing Guarantees that player's state only switch to dead iff all minion's health = 0
    some p: Player |{
        some m : Minion |{
            (m in p.minions)
            (m.mHealth != 0)
            (p.pState = PlayerDead)
        }
    }

}

pred invalid_hero{
    -- Testing Guarantees that only 1 hero option for all player
    some p: Player |{
        p.hero != Nightmare
    }
}



test suite for traces {
    // Test expect combination 
    test expect {
    test1 : {traces implies test_PlayerInitialState} for exactly 2 Player is sat
    test2 : {traces implies noUnexpectMinions}for exactly 2 Player is sat
    test3 : {traces implies validHero} for exactly 2 Player is sat
    test4 : {traces implies has_winner_eventually} for exactly 2 Player is sat
    test5 : {traces implies correct_turn_switch} for exactly 2 Player is sat
    test6 : {traces implies always_some_minion_take_action} for exactly 2 Player is theorem
    test7 : {traces implies health_NoChange_check} for exactly 2 Player is theorem
    test8 : {traces implies health_decresing_check} for exactly 2 Player is theorem
    test9 : {traces implies minion_state_check_A} for exactly 2 Player is sat
    test10 : {traces implies minion_state_check_B} for exactly 2 Player is theorem 
    test11 : {traces implies At_least_one_player_was_terminated} for exactly 2 Player is sat 
    test12 : {traces and some_player_has_no_minions} for exactly 2 Player is unsat 
    test13 : {traces and some_invalid_player} for exactly 2 Player is unsat 
    test14 : {traces and invalid_player_state_switch} for exactly 2 Player is unsat 
    test15 : {traces and invalid_hero} for exactly 2 Player is unsat 
    }
}












