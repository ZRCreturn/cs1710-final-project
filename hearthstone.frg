#lang forge/temporal
option max_tracelength 14



/*********************************************************
*The abstract foundational components of game generation.*
*                        Section 1                       *
**********************************************************/

-- Two Players Total
sig Player{
    var hero: one Hero,
    var servants : set Servant
    var state   : one PlayerState
}
-- We assume the Red player always go first 
one sig Red, Blue extends Player{}

-- Player State Dead/Live
abstract sig PlayerState{}
one sig PlayerDead, PlayerLive extends PlayerState{}

-- 6 Heros with dimplieserent buffs for Player to pick
-- Dimplieserent Heros adding buffs to all Servants of the player
sig Hero{
    var attack  : one Int,
    var defense : one Int,
    var health  : one Int
}
one sig Nightmare, Immortal, Paladin, Lava, Panda, Drunkard extends Hero{}

-- A total of 10 servants for the player to choose from
    -- Explanation：
        -- Each servant has attack damage, defense anti-damage, health status, 
        -- and Hit (indicating whether the servant have attacked the opponent this round)
        -- Servant should not attact opponent over 1 times in one round

sig Servant{
    var attack  : one Int,              -- 伤害 
    var defense : one Int,              -- 防御
    var health  : one Int,              -- 血量
    var hit     : one Hit,              -- 当前round是否攻击过
    var state   : one ServantState      -- 当前round状态 死亡/存活
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10 extends Servant{}

abstract sig Hit{}
one sig AttackCompleted, NotAttacked extends Hit{}

abstract sig ServantState{}
one sig ServantLive, ServantDead extends ServantState{}


/*********************************************************
*                  State predicates checks               *
*                        Section 2                       *
**********************************************************/


-- In this component, we test the initial state.
pred InitPlayerStateSAT{
    all p : Player | {
        (p = Red or p = Blue)
        (p.hero = Nightmare or p.heros = Immortal or p.heros = Paladin or p.heros = Lava or p.heros = Panda orp.heros = Drunkard)
        ((some p.servants)=>{NoSharedServants})
        (p.state = PlayerLive)
    }
}
pred NoSharedServants {
    #{Red.servants & Blue.servants} = 0
}


-- Initialize Heros state, Set unique values to each hero's attack, defense, and health
pred InitHeroStateSAT{
    all h : Hero{
        -- Nightmare
        (h = Nightmare implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
        -- Immortal
        (h = Immortal implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
        -- Paladin
        (h = Paladin implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
        -- Lava
        (h = Lava implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
        -- Panda
        (h = Panda implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
        -- Drunkard
        (h = Drunkard implies {
            h.attack = 
            h.defense = 
            h.health = 
        })
    }
}
-- Initialize all Servant state
pred InitServantStateSAT{
    all s : Servant {
        ((s = S1) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S2) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S3) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S4) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S5) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S6) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S7) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S8) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S9) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
        ((s = S10) implies {
            s.attack = 
            s.defense = 
            s.health = 
            s.hit = NotAttacked
            s.state = ServantLive
        })
    }
}

pred InitStateChecksSAT{
    InitPlayerStateSAT
    InitHeroStateSAT
    InitServantStateSAT
}


-- In this component, We test the safety of actions.
    -- In other word, Am I able to take action safely? Action Guard
pred stayStill[p:Player]{} -- no changes if it is my attack round
pred playerAttackEnable[p : Player]{}
pred servantAttackEnable[p : Player, s: Servant]{}


-- In this component, we test for the correctness of operations (hit or defen)
pred attackCorrectness[]{}
pred defenseCorrectness[]{}
pred healthCalculationCorrectness[]{}
pred CorrectnessLiveOrDeadState[]{}



-- procedures 

pred GamingProcedure{
    -- Core rule of running game
}

-- Trace, run the game  -- since the max teace = 14, we can not set too much health to Servants
-- Please pay attention to the ratio of (attack: defence : Health : trace_length)
trace {
    ...
}



