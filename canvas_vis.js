const canvas = document.createElement("canvas")


canvas.width = 600;
canvas.height = 520;

canvas.style.border = "1px solid black"

div.appendChild(canvas)

const ctx = canvas.getContext("2d")

////////////////////////

const red_minions = Red.join(minions).tuples()
const blue_minions = Blue.join(minions).tuples()

const create_minion_state = (
  health, action, attack, has_shield, has_taunt, has_lifesteal, is_attacker, is_victim
) => ({
  health, action, attack, has_shield, has_taunt, has_lifesteal, is_attacker, is_victim
})

const get_all_game_time_states = (game_time) => {
  if (game_time.empty()) {
    return []
  }

  const next_game_time = game_time.join(Game0.join(next))

  let game_time_state

  if (next_game_time.empty()) {
    const get_minion_states = (minions) => {
      const minion_states = []
      for (const minion of minions) {
        const health = minion.join(game_time.join(tmHealth)).toString()
        const action = minion.join(game_time.join(tmAction)).toString()
        const attack = minion.join(mAttack).toString()
        const has_shield = minion.join(game_time.join(tmSheild)).toString() === 'SheildActive0'
        const has_taunt = minion.join(mTaunt).toString() === 'True0'
        const has_lifesteal = minion.join(mLifesteal).toString() === 'True0'
    
        minion_states.push(create_minion_state(
          health, action, attack, has_shield, has_taunt, has_lifesteal, false, false
        ))
      }
      return minion_states
    }

    game_time_state = {
      game_time: game_time.toString(),
      red_minion_states: get_minion_states(red_minions),
      blue_minion_states: get_minion_states(blue_minions)
    }
  } else {
    const get_minion_states = (minions) => {
      const minion_states = []
      for (const minion of minions) {
        const health = minion.join(game_time.join(tmHealth)).toString()
        const action = minion.join(game_time.join(tmAction)).toString()
        const attack = minion.join(mAttack).toString()
        const has_shield = minion.join(game_time.join(tmSheild)).toString() === 'SheildActive0'
        const has_taunt = minion.join(mTaunt).toString() === 'True0'
        const has_lifesteal = minion.join(mLifesteal).toString() === 'True0'

        const next_health = minion.join(next_game_time.join(tmHealth)).toString()
        const next_action = minion.join(next_game_time.join(tmAction)).toString()
        const next_has_shield = minion.join(next_game_time.join(tmSheild)).toString() === 'SheildActive0'

        const is_attacker = next_action === 'ActionCompleted0' && action === 'NotAction0'
        const is_victim = !is_attacker && ((next_health !== health) || (has_shield && !next_has_shield))

        minion_states.push(create_minion_state(
          health, action, attack, has_shield, has_taunt, has_lifesteal, is_attacker, is_victim
        ))
      }
      return minion_states
    }

    game_time_state = {
      game_time: game_time.toString(),
      red_minion_states: get_minion_states(red_minions),
      blue_minion_states: get_minion_states(blue_minions)
    }
  }
  
  game_time_state.is_end = (game_time.join(end).toString() === 'True0')
  const rest_game_time_states = get_all_game_time_states(next_game_time)

  return [game_time_state, ...rest_game_time_states]
}

const game_time_states = get_all_game_time_states(Game0.join(firstState))
let current_game_time_state_index = 0

const draw_minion_states = (
  minion_states,
  rectangle
) => {
  const minion_rectangle_width = 100
  const minion_rectangle_height = 136

  for (const index in minion_states) {
    const x = 10 + index * rectangle.width / minion_states.length
    const y = rectangle.y + (rectangle.height - minion_rectangle_height) / 2

    ctx.drawImage(minion_image, x, y, minion_rectangle_width, minion_rectangle_height)
    const {
      health, action, attack, has_shield, has_taunt, has_lifesteal, is_attacker, is_victim
    } = minion_states[index]

    ctx.font = '13px Arial Black'
    ctx.fillStyle = 'white'
    ctx.strokeStyle = 'black'
    ctx.lineWidth = 3

    const health_x = x+minion_rectangle_width-16
    const health_y = y+minion_rectangle_height-10
    ctx.strokeText(health, health_x, health_y)
    ctx.fillText(health, health_x, health_y)

    const attack_x = x+12
    const attack_y = y+minion_rectangle_height-10
    ctx.strokeText(attack, attack_x, attack_y)
    ctx.fillText(attack, attack_x, attack_y)

    const shield_text = has_shield ? 'Shield' : ''
    const taunt_text = has_taunt ? 'Taunt' : ''
    const lifesteal_text = has_lifesteal ? 'Lifesteal' : ''

    ctx.font = '11px Arial Black'
    ctx.fillStyle = 'black'
    const property_x = x+minion_rectangle_width/2-23
    ctx.fillText(shield_text, property_x, y+minion_rectangle_height-40)
    ctx.fillText(taunt_text, property_x, y+minion_rectangle_height-28)
    ctx.fillText(lifesteal_text, property_x, y+minion_rectangle_height-16)

    const attacker_victim_x = x + minion_rectangle_width / 2 - 25
    const attacker_victim_y = y + minion_rectangle_height + 15
    let text
    if (is_attacker) {
      text = 'Attacker'
    } else if (is_victim) {
      text = 'Victim'
    } else {
      text = ''
    }
    ctx.font = '13px Arial Black'
    ctx.fillText(text, attacker_victim_x, attacker_victim_y)
  }
}

const create_rectangle = (x, y, width, height) => ({x, y, width, height})

const draw_game_time_state = (current_game_time_state_index) => {

  const game_time_state = game_time_states[current_game_time_state_index]
  let title
  if (game_time_state.is_end) {
    title = 'Game End'
  } else if (current_game_time_state_index % 5 === 4) {
    title = `${game_time_state.game_time}, Turn change`
  } else {
    title = game_time_state.game_time
  }
  ctx.fillStyle = 'black'
  ctx.font = '20px Arial'
  ctx.fillText(title, 250, 30)

  const red_rectangle = create_rectangle(0, 40, 600, 200)
  draw_minion_states(game_time_state.red_minion_states, red_rectangle)
  const blue_rectangle = create_rectangle(0, 300, 600, 200)
  draw_minion_states(game_time_state.blue_minion_states, blue_rectangle)
}

const minion_image = new Image()
minion_image.src = '/Users/forrest/courses/registered/1710/cs1710-final-project/minion1.png'
minion_image.addEventListener(
  'load',
  () => draw_game_time_state(current_game_time_state_index)
)

///////////////////////

const prev_button = document.createElement('button')
prev_button.textContent = 'prev';

prev_button.addEventListener(
  'click',
  () => {
    current_game_time_state_index = (current_game_time_state_index + game_time_states.length - 1) % game_time_states.length
    ctx.clearRect(0, 0, canvas.width, canvas.height)
    draw_game_time_state(current_game_time_state_index)
  }
)

div.appendChild(prev_button)

const span = document.createElement('span')
span.style.width = '20px'
span.style.display = "inline-block"
div.appendChild(span)

const next_button = document.createElement('button')
next_button.textContent = 'next';

next_button.addEventListener(
  'click',
  () => {
    current_game_time_state_index = (current_game_time_state_index + 1) % game_time_states.length
    ctx.clearRect(0, 0, canvas.width, canvas.height)
    draw_game_time_state(current_game_time_state_index)
  }
)

div.appendChild(next_button)

