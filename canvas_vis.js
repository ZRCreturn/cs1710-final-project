const canvas = document.createElement("canvas")


canvas.width = 600;
canvas.height = 520;

canvas.style.border = "1px solid black"

div.appendChild(canvas)

const ctx = canvas.getContext("2d")

////////////////////////

const red_minions = Red.join(minions).tuples()
const blue_minions = Blue.join(minions).tuples()

const create_minion_state = (health, action, is_attacker, is_defender) => ({
  health, action, is_attacker, is_defender
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
    
        minion_states.push(create_minion_state(health, action, false, false))
      }
      return minion_states
    }

    game_time_state = {
      game_time: game_time.toString(),
      red_minion_states: get_minion_states(red_minions),
      blue_minion_states: get_minion_states(blue_minions)
    }

    // const red_minion_states = []
    // for (const red_minion of red_minions) {
    //   const health = red_minion.join(game_time.join(tmHealth)).toString()
    //   const action = red_minion.join(game_time.join(tmAction)).toString()
  
    //   red_minion_states.push(create_minion_state(health, action, false, false))
    // }
  
    // const blue_minion_states = []
    // for (const blue_minion of blue_minions) {
    //   const health = blue_minion.join(game_time.join(tmHealth)).toString()
    //   const action = blue_minion.join(game_time.join(tmAction)).toString()
  
    //   blue_minion_states.push(create_minion_state(health, action, false, false))
    // }
  
    // game_time_state = {
    //   game_time: game_time.toString(),
    //   red_minion_states,
    //   blue_minion_states
    // }
  } else {
    const get_minion_states = (minions) => {
      const minion_states = []
      for (const minion of minions) {
        const health = minion.join(game_time.join(tmHealth)).toString()
        const action = minion.join(game_time.join(tmAction)).toString()

        const next_health = minion.join(next_game_time.join(tmHealth)).toString()
        const next_action = minion.join(next_game_time.join(tmAction)).toString()

        const is_attacker = next_action !== action
        const is_defender = !is_attacker && (next_health !== health)

        minion_states.push(create_minion_state(health, action, is_attacker, is_defender))
      }
      return minion_states
    }

    game_time_state = {
      game_time: game_time.toString(),
      red_minion_states: get_minion_states(red_minions),
      blue_minion_states: get_minion_states(blue_minions)
    }
  }
  
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
  
    // ctx.strokeRect(x, y, minion_rectangle_width, minion_rectangle_height)
    ctx.drawImage(minion_image, x, y, minion_rectangle_width, minion_rectangle_height)
    const {health, action, is_attacker, is_defender} = minion_states[index]
    // const lines = [
    //   `HP: ${health}`,
    //   `${action}`
    // ]
    // if (is_attacker) {
    //   lines.push('ATTACKER')
    // }

    // if (is_defender) {
    //   lines.push('DEFENDER')
    // }

    // const line_height = 30

    // ctx.font = '20px Arial'

    // for (let i = 0; i < lines.length; i++) {
    //   ctx.fillText(lines[i], x+5, y + 20 + i * line_height);
    // }

    ctx.fillStyle = 'white'
    ctx.font = '13px Arial Black'
    ctx.fillText(health, x+minion_rectangle_width-16, y+minion_rectangle_height-10)
  }
}

const create_rectangle = (x, y, width, height) => ({x, y, width, height})

const draw_game_time_state = (game_time_state) => {
  ctx.fillStyle = 'black'
  ctx.font = '20px Arial'
  ctx.fillText(`${game_time_state.game_time}`, 300, 30)

  const red_rectangle = create_rectangle(0, 40, 600, 200)
  draw_minion_states(game_time_state.red_minion_states, red_rectangle)
  const blue_rectangle = create_rectangle(0, 300, 600, 200)
  draw_minion_states(game_time_state.blue_minion_states, blue_rectangle)
}

const minion_image = new Image()
minion_image.src = '/Users/forrest/courses/registered/1710/cs1710-final-project/minion1.png'
minion_image.addEventListener(
  'load',
  () => draw_game_time_state(game_time_states[current_game_time_state_index])
)

///////////////////////

const prev_button = document.createElement('button')
prev_button.textContent = 'prev';

prev_button.addEventListener(
  'click',
  () => {
    current_game_time_state_index = (current_game_time_state_index + game_time_states.length - 1) % game_time_states.length
    ctx.clearRect(0, 0, canvas.width, canvas.height)
    draw_game_time_state(game_time_states[current_game_time_state_index])
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
    draw_game_time_state(game_time_states[current_game_time_state_index])
  }
)

div.appendChild(next_button)

