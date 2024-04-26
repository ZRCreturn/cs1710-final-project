#lang forge/temporal
open "hearthstone.frg"

/****************************************
* Section 1 : Init State Test           * 
****************************************/


-- 1.1 Player Init state testing 
pred test_PlayerInitialState {
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
    all h: Hero | {
        (p.hero = h ) => {h.hHealth > 0}
    }
}
pred validMinionState[p : Player]{
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
    #{Red.minions & Blue.minions} = 0
}

-- Init Case testing

    --1.2 Minions testing
pred noUnexpectMinions {
    all m : Minion {
        always{((m = S1) or (m = S2) or (m = S3) or 
        (m = S4) or (m = S5) or (m = S6) or 
        (m = S7) or (m = S8) or (m = S9) or 
        (m = S10))}
    }
}
    --1.3 Hero state s --> s' undead checking 
pred validHero {
    always{all h : Hero {
        h.hHealth > 0
    }}
}

/****************************************
* Section 2 : State transfer test       * 
****************************************/

pred has_winner_eventually {
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

pred correct_turn_switch{
    always (all t : GameTime | {
        t.turn != t'.turn
    })
}

pred always_some_minion_take_action {
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

pred health_NoChange_check {
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

// test

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
}