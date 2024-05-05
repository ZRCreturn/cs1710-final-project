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
        (m = S4) or (m = S5) or (m = S6) or 
        (m = S7) or (m = S8))
    }
}

/* New test adding */

    -- No Game State.next points to First state, Acyclic TEST
pred noFirstStatePrev{
    all t : GameTime |{
        Game.next[t] != Game.firstState
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
        ((t1 != t2) and (Game.next[t1] = t2)) => {(Game.next[t2] != Game.firstState)}
    }
}
    -- No Circle
pred noCircleTest{
        all t1, t2 : GameTime |{
        ((t1 != t2) and (Game.next[t1] = t2)) implies {Game.next[t2] != t1}
    }
}



/*-------------------------------------------------*\
|   Game Procedure Properties + Verification   |
\*-------------------------------------------------*/
    --ALL PLAYER WELL-FORMED 
pred wellformed{
    -- Check all objects initial status
    one t : GameTime |{
        (Game.firstState = t)
        wellformed_minions
        wellformed_hero
        wellformed_player
        wellformed_gameTime
    }
}
pred wellformed_minions{
    -- WellFormed helper function 1
    all m : Minion |{
        ((m in Red.minions) or (m in Blue.minions))
        (m.mAttack <= 7)
        (m.mHealth <= 7)
        (m.mAction = NotAction)
        (m.mState = MinionLive)
        ((m.mSheild = SheildActive)or(m.mSheild = SheildBroken))
        ((m.mTaunt = True) or (m.mTaunt = False))
    }
}
pred wellformed_hero{
    -- WellFormed helper function 2
    (Nightmare.hHealth > 0)
    (Red.hero = Nightmare)
    (Blue.hero =Nightmare)
}
pred wellformed_player{
    -- WellFormed helper function 3
    one t : GameTime |{
        (Game.firstState = t)
        (all p : Player | {
            (p.hero = Nightmare)
            (#{p.minions} = 4)
            (#{Red.minions & Blue.minions} = 0)
            (p.pState = PlayerLive)
        })
    }
}
pred wellformed_gameTime{
    -- WellFormed helper function 4
    one t : GameTime {
        (Game.firstState = t)
        (t.turn = Blue)
    }
}

/* Player Special Function Tests -- Lifesteal, sheild, and Taunt */
    -- NO CHANGE ON MINIONS HEALTH POINTS IF THE CURRENT IS IT'S LORD PLAYER
pred attacker_minions_health_StaySame_if_sheild [p : Player]{
    -- Testing Guarantees No change in minion health when the current turn is its master's attack
    all t1, t2: GameTime |{
        (Game.next[t1] = t2)
        (t1.turn = p)
        (all m : Minion |{
            ((m in p.minions) and (m.mSheild = SheildActive)) implies{
                t1.tmHealth[m] = t2.tmHealth[m]
            }
        })
    }
}

    -- ALL MINION'S HEALTH POINTS = MINION.CURRENT-HEALTH - ATTCK POINTS FROM OTHER MINIONS
pred attacker_minions_health_drop_if_nonSheild[p : Player]{
    -- Testing Guarantees the m.health drop is calculated correctly when the minion is attacked.
    all prev, post : GameTime |{
        (Game.next[prev] = post)
        (prev.turn = p)
        (all m : Minion |{
            ((m in p.minions) and (m.mSheild = SheildBroken)) implies {
                (prev.tmHealth[m] = post.tmHealth[m]) or (
                    some m_vit : Minion |{
                       (m_vit not in p)
                       (m_vit.mAttack = prev.tmHealth[m] - post.tmHealth[m])
                    }
                )
            }
        })
    }
}

    -- ALL minions with Lift steal ON and sheild On should steal health from attack
        -- The number of points stealed should be equal to it's attack points
pred attacker_Lifesteal_check[p : Player]{
    all m : Minion | {
        (m in p.minions)
        (m.mLifesteal = True)
        (m.mSheild = SheildActive)
        some t1, t2 : GameTime | {
            (Game.next[t1] = t2)
            t2.tmHealth[m] = t1.tmHealth[m] + m.mAttack
        }
    }
}

    -- Test if the Minion m1 with skill Taunt On, No one should be attacked before m1 is attacked.
pred victim_Taunt_check[p: Player]{
    all prev, post : GameTime | {
        (Game.next[prev] = post)
        (some m1, m2: Minion | {
            (prev.turn = Red)
            (post.turn = Blue)
            (m1 != m2) and 
            (m1 in Blue.minions) and 
            (m2 in Blue.minions) and
            (m1.mTaunt = True)and
            (m1.mSheild = SheildBroken)and
            (m2.mTaunt = False)and
            (m2.mSheild = SheildBroken) and 
            (prev.tmHealth[m2] != post.tmHealth[m2]) and 
            (prev.tmHealth[m1] = post.tmHealth[m1])
        })
    }
}

    -- IF minion m is victim in current turn and lift steal ON, and m survived after the attack，
        -- m shold steal some health point at current round fight back
pred victim_sheild_function_check[p : Player]{
    some m : Minion, attk_t, vict_t :GameTime| {
        ((m not in attk_t.turn.minions) and 
        (Game.next[attk_t] = vict_t)and
        (attk_t.tmSheild[m] = SheildActive) and 
        (vict_t.tmSheild[m] = SheildBroken)) implies {
            attk_t.tmHealth[m] = vict_t.tmHealth[m]
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
        some m : Minion |{
            (m in t1.turn.minions)
            (t1.tmState[m] != t2.tmState[m])
        }
    }
}

test suite for traces {

    test expect {
        -- BASIC PROPERTY TESTS
        PROPERTY_BASED_TEST1 : {traces and only_two_player_join_the_game} is sat
        PROPERTY_BASED_TEST2 : {traces and all_hero_init_health_greater_than_zero[Player]}for exactly 2 Player is sat
        PROPERTY_BASED_TEST3 : {traces and always_keep_validHero[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST4 : {traces and all_minion_sat_init_setup[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST5 : {traces and noSharedMinions[Player]} for exactly 2 Player is sat
        PROPERTY_BASED_TEST6 : {traces implies noUnexpectMinions} is theorem
        PROPERTY_BASED_TEST7 : {traces implies noFirstStatePrev} is theorem
        PROPERTY_BASED_TEST8 : {traces implies noEndingStateNext} is theorem
        PROPERTY_BASED_TEST9 : {traces implies noFirstStatePrevReachable} is theorem
        PROPERTY_BASED_TEST10 : {traces implies noCircleTest} is theorem

		-- OPERATIONAL TEST
        OPERATIONAL_TEST1 : {traces and wellformed} is sat
        OPERATIONAL_TEST2 : {traces implies attacker_minions_health_StaySame_if_sheild[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST3 : {traces implies attacker_minions_health_drop_if_nonSheild[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST4 : {traces implies minion_state_check_A} is sat
        OPERATIONAL_TEST5 : {traces implies minion_state_check_B} is sat
        OPERATIONAL_TEST6 : {traces and some_player_has_no_minions [Player]}for exactly 2 Player is unsat
        OPERATIONAL_TEST7 : {traces and invalid_player_state_switch[Player]}for exactly 2 Player is unsat
        OPERATIONAL_TEST8 : {traces implies attacker_Lifesteal_check[Player]}for exactly 2 Player is sat
        OPERATIONAL_TEST9 : {traces and victim_Taunt_check[Player]}for exactly 2 Player is unsat
        OPERATIONAL_TEST10 : {traces and victim_sheild_function_check[Player]}for exactly 2 Player is sat

        -- LIVENESS TEST
        LIVENESS_TEST_A : {traces implies has_winner_eventually} is sat
        -- STARVATION FREE TEST
        STARVATION_FREE_TEST_A : {traces implies correct_turn_switch} is sat
        STARVATION_FREE_TEST_B : {traces implies always_some_minion_take_action} is sat 

    }
}












